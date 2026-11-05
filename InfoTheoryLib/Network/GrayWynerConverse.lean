/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.SupportLemma
public import InfoTheoryLib.Network.BergerTungOuter
public import InfoTheoryLib.Network.GrayWyner
public import InfoTheoryLib.Network.MDCases

/-!
# The Gray–Wyner theorem

This file proves the converse of the Gray–Wyner theorem, a cardinality bound on `V`, and the theorem
itself, Theorem 3 of Lecture 15 of El Gamal and Kim: the optimal rate region is the set of the rate
triples with `R₀ ≥ I(U₁, U₂; V)`, `R₁ ≥ H(U₁|V)` and `R₂ ≥ H(U₂|V)` for some `p(v|u₁, u₂)`.

## Main definitions

* `gwSet P N`: the rate triples of the theorem, for `V` with `N` values.

## Main statements

* `GWCode.exists_channel`: the single-letter bounds for one code, with
  `Vᵢ = (M₀, U₁ⁱ⁻¹, U₂ⁱ⁻¹)`.
* `exists_gw_reduce`: the cardinality bound `|𝒱| ≤ |𝒰₁| |𝒰₂| + 4`.
* `isClosed_gwSet`: the set of the rate triples is closed.
* `gwRegion_eq`: **the Gray–Wyner theorem**.
* `mem_gwRegion_of_channel`, `gwRegion_subset_gwSet`: the two directions, the first one for
  `V` on any finite set.

## Implementation notes

The notes have `|𝒱| ≤ |𝒰₁| |𝒰₂| + 2`, from the Fenchel–Eggleston strengthening of Carathéodory's
theorem and the constraint that a pmf sums to one. We use Carathéodory's theorem in the whole space,
which is all that the compactness argument needs.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ} {n M₀ M₁ M₂ : ℕ}

/-! ### The bounds for one code -/

section Code

/-- **Lecture 15, page 15-23.** `∑ᵢ H(pr(Zᵢ) | M₀, Zⁱ⁻¹) ≤ log M + H(pr(Z)ⁿ | M, M₀)`, and Fano's
inequality. -/
lemma sum_condEntropy_le_gw {a : Type*} [Fintype a] (hP : IsPMF P) (z₀ : α₁ × α₂)
    (pr : α₁ × α₂ → a) (A₀ : (Fin n → α₁ × α₂) → Fin M₀) {M : ℕ} (A : (Fin n → α₁ × α₂) → Fin M)
    (dec : Fin M × Fin M₀ → Fin n → a) :
    ∑ i : Fin n, H[fun ω : Fin n → α₁ × α₂ => pr (ω i) | pair A₀ (prefixRV (seqZ z₀) i) ;
        iidPMF P n] ≤
      log M + log 2 + errProb (iidPMF P n) (fun ω j => pr (ω j)) (pair A A₀) dec *
        (n * log (Fintype.card a)) := by
  classical
  have hμ := iidPMF_isPMF hP n
  set Xk : ℕ → (Fin n → α₁ × α₂) → a := fun k ω => pr (seqZ z₀ k ω) with hXk
  have hchain := chain_rule_entropy_cond hμ Xk A₀ n
  have hprefix : prefixRV Xk n = fun (ω : Fin n → α₁ × α₂) j => pr (ω j) := by
    funext ω j
    simp only [prefixRV, hXk, seqZ_coe]
  rw [hprefix, sum_range] at hchain
  have hmore : ∀ i : Fin n, H[fun ω : Fin n → α₁ × α₂ => pr (ω i) |
      pair A₀ (prefixRV (seqZ z₀) i) ; iidPMF P n] ≤
      H[Xk i | pair A₀ (prefixRV Xk i) ; iidPMF P n] := fun i => by
    have hX : Xk i = fun ω : Fin n → α₁ × α₂ => pr (ω i) := funext fun ω => by
      simp only [hXk, seqZ_coe]
    rw [hX]
    exact condEntropy_le_condEntropy_comp hμ _ (pair A₀ (prefixRV (seqZ z₀) i))
      (fun w => (w.1, fun j => pr (w.2 j)))
  refine (sum_le_sum fun i _ => hmore i).trans ?_
  rw [← hchain]
  have hfano := fano_weak hμ (fun (ω : Fin n → α₁ × α₂) j => pr (ω j)) (pair A A₀) dec
  have hcard : log (Fintype.card (Fin n → a)) = n * log (Fintype.card a) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  rw [hcard] at hfano
  have hsub := condEntropy_sub_condEntropy_le hμ (fun (ω : Fin n → α₁ × α₂) j => pr (ω j)) A A₀
  linarith

/-- The probability of error of one decoder is at most that of the code. -/
lemma errProb_le_gw (c : GWCode M₀ M₁ M₂ n α₁ α₂) (hP : IsPMF P) :
    errProb (iidPMF P n) (fun (ω : Fin n → α₁ × α₂) j => (ω j).1) (pair c.enc₁ c.enc₀)
        (fun m => c.dec₁ (m.2, m.1)) ≤ c.errProb P ∧
      errProb (iidPMF P n) (fun (ω : Fin n → α₁ × α₂) j => (ω j).2) (pair c.enc₂ c.enc₀)
        (fun m => c.dec₂ (m.2, m.1)) ≤ c.errProb P := by
  classical
  have hμ := iidPMF_isPMF hP n
  constructor
  · refine sum_le_sum fun ω _ => ?_
    by_cases h : c.dec₁ (c.enc₀ ω, c.enc₁ ω) = fstSeq ω
    · have h' : c.dec₁ (c.enc₀ ω, c.enc₁ ω) = fun j => (ω j).1 := h
      simp only [pair, h', ne_eq, not_true_eq_false, ite_false]
      exact mul_nonneg (hμ.nonneg ω) (by split_ifs <;> norm_num)
    · have h' : ¬ c.dec₁ (c.enc₀ ω, c.enc₁ ω) = fun j => (ω j).1 := h
      simp [pair, h', h]
  · refine sum_le_sum fun ω _ => ?_
    by_cases h : c.dec₂ (c.enc₀ ω, c.enc₂ ω) = sndSeq ω
    · have h' : c.dec₂ (c.enc₀ ω, c.enc₂ ω) = fun j => (ω j).2 := h
      simp only [pair, h', ne_eq, not_true_eq_false, ite_false]
      exact mul_nonneg (hμ.nonneg ω) (by split_ifs <;> norm_num)
    · have h' : ¬ c.dec₂ (c.enc₀ ω, c.enc₂ ω) = fun j => (ω j).2 := h
      simp [pair, h', h]

/-- The conditional entropies of the source components under the time sharing. -/
lemma condEntropy_gw_mix {a : Type*} [Fintype a] (hP : IsPMF P) (hn : 0 < n) (z₀ : α₁ × α₂)
    (A₀ : (Fin n → α₁ × α₂) → Fin M₀) {k : ℕ}
    (e : (Σ i : Fin n, Fin M₀ × (Fin i → α₁ × α₂)) ≃ Fin k) {κ : α₁ × α₂ → Fin k → ℝ}
    (hL : jointOf P κ = dist (mixLaw (iidPMF P n) (Fin n)) fun z =>
      (z.1 z.2, e ⟨z.2, A₀ z.1, prefixRV (seqZ z₀) z.2 z.1⟩)) (pr : α₁ × α₂ → a) :
    H[fun z : (α₁ × α₂) × Fin k => pr z.1 | Prod.snd ; jointOf P κ] =
      (n : ℝ)⁻¹ * ∑ i : Fin n, H[fun ω : Fin n → α₁ × α₂ => pr (ω i) |
        pair A₀ (prefixRV (seqZ z₀) i) ; iidPMF P n] := by
  classical
  have hμ := iidPMF_isPMF hP n
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  have h1 := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α₁ × α₂) => pr (ω i))
    (b := fun i : Fin n => Fin M₀ × (Fin i → α₁ × α₂))
    fun i => pair A₀ (prefixRV (seqZ z₀) i)
  simp only [Fintype.card_fin] at h1
  rw [← h1, hL, ← condEntropy_comp_comp hν _]
  exact condEntropy_congr_right hν _ e e.injective fun _ => rfl

/-- **The converse of Theorem 3 for one code (Lecture 15, page 15-23).** The auxiliary random
variable is `V = (Q, M₀, U₁^{Q-1}, U₂^{Q-1})`, for a uniform time `Q`. -/
theorem GWCode.exists_channel (hP : IsPMF P) (hn : 0 < n) (c : GWCode M₀ M₁ M₂ n α₁ α₂) :
    ∃ (k : ℕ) (κ : α₁ × α₂ → Fin k → ℝ), IsChannel κ ∧ n * gwInfo P κ ≤ log M₀ ∧
      n * gwCond₁ P κ ≤ log M₁ + log 2 + c.errProb P * (n * log (Fintype.card α₁)) ∧
      n * gwCond₂ P κ ≤ log M₂ + log 2 + c.errProb P * (n * log (Fintype.card α₂)) := by
  classical
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  set ν := mixLaw (iidPMF P n) (Fin n) with hνd
  set e := Fintype.equivFin (Σ i : Fin n, Fin M₀ × (Fin i → α₁ × α₂)) with he
  set S : Fin n → (Fin n → α₁ × α₂) → Σ i : Fin n, Fin M₀ × (Fin i → α₁ × α₂) :=
    fun i ω => ⟨i, c.enc₀ ω, prefixRV (seqZ z₀) i ω⟩ with hS
  set W : (Fin n → α₁ × α₂) × Fin n → (α₁ × α₂) × Fin _ := fun z => (z.1 z.2, e (S z.2 z.1)) with hW
  have hr : IsPMF (dist ν W) := hν.dist W
  have hk : Nonempty (Fin (Fintype.card (Σ i : Fin n, Fin M₀ × (Fin i → α₁ × α₂)))) := by
    obtain ⟨z⟩ : Nonempty ((Fin n → α₁ × α₂) × Fin n) := ⟨(fun _ => z₀, ⟨0, hn⟩)⟩
    exact ⟨(W z).2⟩
  obtain ⟨κ, hκ, hker⟩ := exists_kernel hr
  have hfst : dist (dist ν W) Prod.fst = P := by
    rw [← dist_comp_eq]
    exact dist_mix_coord hP hn
  have hL : jointOf P κ = dist ν W := by
    funext ⟨a, b⟩
    rw [hker a b, hfst]
    rfl
  have hLP : IsPMF (jointOf P κ) := jointOf_isPMF hP hκ
  have hinv : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn'.ne'
  have hHZ : H[Prod.fst ; jointOf P κ] = entropy P := by
    rw [entropyRV, dist_jointOf_fst hκ]
  have hHn : H[id ; iidPMF P n] = n * entropy P := by
    rw [entropyRV, dist_id, entropy_iidPMF hP]
  refine ⟨_, κ, hκ, ?_, ?_, ?_⟩
  · -- The bound on `R₀`.
    have h1 := condEntropy_mix_prefix_of_inj z₀ hP hn c.enc₀ (fun z => e (S z.2 z.1)) e
      e.injective fun z => rfl
    have h2 : H[Prod.fst | Prod.snd ; jointOf P κ] = (n : ℝ)⁻¹ * H[id | c.enc₀ ; iidPMF P n] := by
      rw [← h1, hL, ← condEntropy_comp_comp hν W]
      rfl
    have h3 : H[id ; iidPMF P n] - H[id | c.enc₀ ; iidPMF P n] ≤ log M₀ := by
      rw [← mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_comm hμ,
        mutualInfo_eq_entropy_sub_condEntropy hμ]
      have a1 := condEntropy_nonneg hμ c.enc₀ (id : (Fin n → α₁ × α₂) → _)
      have a2 := entropyRV_le_log_card hμ c.enc₀
      rw [Fintype.card_fin] at a2
      linarith
    rw [gwInfo, mutualInfo_eq_entropy_sub_condEntropy hLP, hHZ, h2, mul_sub, ← mul_assoc, hinv,
      one_mul, ← hHn]
    exact h3
  · -- The bound on `R₁`.
    have h1 := sum_condEntropy_le_gw hP z₀ (fun z => z.1) c.enc₀ c.enc₁
      (fun m => c.dec₁ (m.2, m.1))
    have hn0 : (0 : ℝ) ≤ n * log (Fintype.card α₁) :=
      mul_nonneg hn'.le (log_natCast_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right (errProb_le_gw c hP).1 hn0
    have h3 : gwCond₁ P κ = (n : ℝ)⁻¹ * ∑ i : Fin n, H[fun ω : Fin n → α₁ × α₂ => (ω i).1 |
        pair c.enc₀ (prefixRV (seqZ z₀) i) ; iidPMF P n] :=
      condEntropy_gw_mix hP hn z₀ c.enc₀ e hL fun z => z.1
    rw [h3, ← mul_assoc, hinv, one_mul]
    linarith
  · -- The bound on `R₂`.
    have h1 := sum_condEntropy_le_gw hP z₀ (fun z => z.2) c.enc₀ c.enc₂
      (fun m => c.dec₂ (m.2, m.1))
    have hn0 : (0 : ℝ) ≤ n * log (Fintype.card α₂) :=
      mul_nonneg hn'.le (log_natCast_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right (errProb_le_gw c hP).2 hn0
    have h3 : gwCond₂ P κ = (n : ℝ)⁻¹ * ∑ i : Fin n, H[fun ω : Fin n → α₁ × α₂ => (ω i).2 |
        pair c.enc₀ (prefixRV (seqZ z₀) i) ; iidPMF P n] :=
      condEntropy_gw_mix hP hn z₀ c.enc₀ e hL fun z => z.2
    rw [h3, ← mul_assoc, hinv, one_mul]
    linarith

end Code

/-! ### The cardinality bound -/

section Reduce

variable {Z υ : Type*} [Fintype Z] [Fintype υ] {Q : Z → ℝ} {κ : Z → υ → ℝ}

/-- If `p(z) κ(u|z) = w(u) r(z|u)`, then `H(A(Z)|U) = ∑ᵤ w(u) H_{r(·|u)}(A(Z))`. -/
lemma condEntropy_of_rep {a : Type*} [Fintype a] (hQ : IsPMF Q) (hκ : IsChannel κ) {w : υ → ℝ}
    {r : υ → Z → ℝ} (hw : IsPMF w) (hr : IsChannel r) (hrep : ∀ z u, Q z * κ z u = w u * r u z)
    (A : Z → a) :
    H[fun z : Z × υ => A z.1 | Prod.snd ; jointOf Q κ] = ∑ u, w u * entropy (dist (r u) A) := by
  have hm : IsChannel (margCh r A) := margCh_isChannel hr A
  have h := condEntropy_jointOf hw hm
  refine Eq.trans ?_ h
  refine condEntropy_eq_of_dist_pair_eq (jointOf_isPMF hQ hκ) (jointOf_isPMF hw hm) ?_
  rw [dist_pair_fst_snd, jointOf_margCh]
  have hsw : jointOf w r = dist (jointOf Q κ) Prod.swap := by
    funext ⟨u, z⟩
    have := dist_comp_of_injective (jointOf Q κ) id Prod.swap_injective (z, u)
    rw [dist_id] at this
    have e : dist (jointOf Q κ) Prod.swap (u, z) = jointOf Q κ (z, u) := this
    rw [e]
    exact (hrep z u).symm
  rw [hsw, ← dist_comp_eq]
  rfl

/-- `H(Z|U)`, as a special case. -/
lemma mutualInfo_of_rep (hQ : IsPMF Q) (hκ : IsChannel κ) {w : υ → ℝ} {r : υ → Z → ℝ}
    (hw : IsPMF w) (hr : IsChannel r) (hrep : ∀ z u, Q z * κ z u = w u * r u z) :
    I[Prod.fst : Prod.snd ; jointOf Q κ] = entropy Q - ∑ u, w u * entropy (r u) := by
  rw [mutualInfo_eq_entropy_sub_condEntropy (jointOf_isPMF hQ hκ), entropyRV, dist_jointOf_fst hκ]
  have h := condEntropy_of_rep hQ hκ hw hr hrep id
  have e : ∀ u, dist (r u) (id : Z → Z) = r u := fun u => dist_id _
  simp only [e] at h
  rw [← h]
  rfl

/-- Every `p(z) p(u|z)` is `w(u) r(z|u)`. -/
lemma exists_rep_channel [Nonempty Z] (hQ : IsPMF Q) (hκ : IsChannel κ) :
    ∃ (w : υ → ℝ) (r : υ → Z → ℝ), IsPMF w ∧ IsChannel r ∧ ∀ z u, Q z * κ z u = w u * r u z := by
  have hJ : IsPMF (dist (jointOf Q κ) Prod.swap) := (jointOf_isPMF hQ hκ).dist _
  obtain ⟨r, hr, hk⟩ := exists_kernel hJ
  refine ⟨_, r, hJ.dist Prod.fst, hr, fun z u => ?_⟩
  have := dist_comp_of_injective (jointOf Q κ) id Prod.swap_injective (z, u)
  rw [dist_id] at this
  have e : dist (jointOf Q κ) Prod.swap (u, z) = jointOf Q κ (z, u) := this
  rw [← hk, e]
  rfl

end Reduce

section Reduce₂

variable {υ : Type*} [Fintype υ] {κ : α₁ × α₂ → υ → ℝ}

/-- **The cardinality bound (Lecture 15, page 15-23, and Appendix C).** The three quantities of the
Gray–Wyner theorem do not change if `V` is replaced by a random variable with
`|𝒰₁| |𝒰₂| + 4` values. -/
theorem exists_gw_reduce (hP : IsPMF P) (hκ : IsChannel κ) {N : ℕ}
    (hN : N = Fintype.card (α₁ × α₂) + 4) :
    ∃ κ' : α₁ × α₂ → Fin N → ℝ, IsChannel κ' ∧ gwInfo P κ' = gwInfo P κ ∧
      gwCond₁ P κ' = gwCond₁ P κ ∧ gwCond₂ P κ' = gwCond₂ P κ := by
  classical
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty (α₁ × α₂) := ⟨z₀⟩
  obtain ⟨w, r, hw, hr, hrep⟩ := exists_rep_channel hP hκ
  set v : υ → ((α₁ × α₂) → ℝ) × ℝ × ℝ × ℝ := fun u =>
    (r u, entropy (r u), entropy (dist (r u) Prod.fst), entropy (dist (r u) Prod.snd)) with hv
  have hdim : N = Module.finrank ℝ (((α₁ × α₂) → ℝ) × ℝ × ℝ × ℝ) + 1 := by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_self, hN]
  subst hdim
  obtain ⟨g, w', hw0, hw1, hsum⟩ := exists_fin_mean_eq hw.nonneg hw.sum_eq_one v
  have key : ∀ L : (((α₁ × α₂) → ℝ) × ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ,
      ∑ j, w' j * L (v (g j)) = ∑ u, w u * L (v u) := fun L => by
    have e := congrArg L hsum
    simpa only [map_sum, map_smul, smul_eq_mul] using e
  have h1 : ∀ z, ∑ j, w' j * r (g j) z = P z := fun z => by
    have e : ∑ j, w' j * r (g j) z = ∑ u, w u * r u z :=
      key ((LinearMap.proj z).comp (LinearMap.fst ℝ ((α₁ × α₂) → ℝ) (ℝ × ℝ × ℝ)))
    rw [e, ← mul_one (P z), ← (hκ z).sum_eq_one, mul_sum]
    exact (sum_congr rfl fun u _ => hrep z u).symm
  have h2 : ∑ j, w' j * entropy (r (g j)) = ∑ u, w u * entropy (r u) :=
    key ((LinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (LinearMap.snd ℝ ((α₁ × α₂) → ℝ) (ℝ × ℝ × ℝ)))
  have h3 : ∑ j, w' j * entropy (dist (r (g j)) Prod.fst) =
      ∑ u, w u * entropy (dist (r u) Prod.fst) :=
    key ((LinearMap.fst ℝ ℝ ℝ).comp ((LinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (LinearMap.snd ℝ ((α₁ × α₂) → ℝ) (ℝ × ℝ × ℝ))))
  have h4 : ∑ j, w' j * entropy (dist (r (g j)) Prod.snd) =
      ∑ u, w u * entropy (dist (r u) Prod.snd) :=
    key ((LinearMap.snd ℝ ℝ ℝ).comp ((LinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (LinearMap.snd ℝ ((α₁ × α₂) → ℝ) (ℝ × ℝ × ℝ))))
  have hw'P : IsPMF w' := ⟨hw0, hw1⟩
  have hr' : IsChannel fun j => r (g j) := fun j => hr (g j)
  -- The new channel.
  have hQ := jointOf_isPMF hw'P hr'
  have hQ' : IsPMF (dist (jointOf w' fun j => r (g j)) Prod.swap) := hQ.dist _
  obtain ⟨j₀⟩ : Nonempty (Fin (Module.finrank ℝ (((α₁ × α₂) → ℝ) × ℝ × ℝ × ℝ) + 1)) :=
    ⟨⟨0, Nat.succ_pos _⟩⟩
  have : Nonempty (Fin (Module.finrank ℝ (((α₁ × α₂) → ℝ) × ℝ × ℝ × ℝ) + 1)) := ⟨j₀⟩
  obtain ⟨κ', hκ', hk⟩ := exists_kernel hQ'
  have hval : ∀ z j, dist (jointOf w' fun j => r (g j)) Prod.swap (z, j) = w' j * r (g j) z :=
    fun z j => by
      have := dist_comp_of_injective (jointOf w' fun j => r (g j)) id Prod.swap_injective (j, z)
      rw [dist_id] at this
      exact this
  have hmarg : ∀ z, dist (dist (jointOf w' fun j => r (g j)) Prod.swap) Prod.fst z = P z :=
    fun z => by
      rw [dist_fst]
      simp only [hval]
      exact h1 z
  have hrep' : ∀ z j, P z * κ' z j = w' j * r (g j) z := fun z j => by
    rw [← hval, hk z j, hmarg]
  refine ⟨κ', hκ', ?_, ?_, ?_⟩
  · simp only [gwInfo]
    rw [mutualInfo_of_rep hP hκ' hw'P hr' hrep', mutualInfo_of_rep hP hκ hw hr hrep, h2]
  · simp only [gwCond₁]
    have a1 := condEntropy_of_rep hP hκ' hw'P hr' hrep' (Prod.fst : α₁ × α₂ → α₁)
    have a2 := condEntropy_of_rep hP hκ hw hr hrep (Prod.fst : α₁ × α₂ → α₁)
    rw [h3] at a1
    exact a1.trans a2.symm
  · simp only [gwCond₂]
    have a1 := condEntropy_of_rep hP hκ' hw'P hr' hrep' (Prod.snd : α₁ × α₂ → α₂)
    have a2 := condEntropy_of_rep hP hκ hw hr hrep (Prod.snd : α₁ × α₂ → α₂)
    rw [h4] at a1
    exact a1.trans a2.symm

end Reduce₂

/-! ### The theorem -/

section Theorem

/-- **Theorem 3 of Lecture 15 of [elgamal2010], page 15-22.** The rate triples, in bits, with
`R₀ ≥ I(U₁, U₂; V)`, `R₁ ≥ H(U₁|V)` and `R₂ ≥ H(U₂|V)` for some `p(v|u₁, u₂)`, with `V` taking `N`
values. -/
def gwSet (P : α₁ × α₂ → ℝ) (N : ℕ) : Set (ℝ × ℝ × ℝ) :=
  {R | ∃ κ : α₁ × α₂ → Fin N → ℝ, IsChannel κ ∧ gwInfo P κ ≤ R.1 * log 2 ∧
    gwCond₁ P κ ≤ R.2.1 * log 2 ∧ gwCond₂ P κ ≤ R.2.2 * log 2}

/-- The set of the rate triples of the theorem is closed. -/
theorem isClosed_gwSet (hP : IsPMF P) (N : ℕ) : IsClosed (gwSet P N) := by
  set F₀ : (α₁ × α₂ → Fin N → ℝ) → ℝ := fun κ =>
    H[Prod.fst ; jointOf P κ] + H[Prod.snd ; jointOf P κ] -
      H[pair Prod.fst Prod.snd ; jointOf P κ] with hF₀
  set F₁ : (α₁ × α₂ → Fin N → ℝ) → ℝ := fun κ =>
    H[pair Prod.snd (fun z : (α₁ × α₂) × Fin N => z.1.1) ; jointOf P κ] -
      H[Prod.snd ; jointOf P κ] with hF₁
  set F₂ : (α₁ × α₂ → Fin N → ℝ) → ℝ := fun κ =>
    H[pair Prod.snd (fun z : (α₁ × α₂) × Fin N => z.1.2) ; jointOf P κ] -
      H[Prod.snd ; jointOf P κ] with hF₂
  have hc₀ : Continuous F₀ :=
    ((continuous_entropyRV_jointOf P _).add (continuous_entropyRV_jointOf P _)).sub
      (continuous_entropyRV_jointOf P _)
  have hc₁ : Continuous F₁ :=
    (continuous_entropyRV_jointOf P _).sub (continuous_entropyRV_jointOf P _)
  have hc₂ : Continuous F₂ :=
    (continuous_entropyRV_jointOf P _).sub (continuous_entropyRV_jointOf P _)
  have hr₀ : Continuous fun p : (α₁ × α₂ → Fin N → ℝ) × ℝ × ℝ × ℝ => p.2.1 * log 2 :=
    (continuous_fst.comp continuous_snd).mul continuous_const
  have hr₁ : Continuous fun p : (α₁ × α₂ → Fin N → ℝ) × ℝ × ℝ × ℝ => p.2.2.1 * log 2 :=
    (continuous_fst.comp (continuous_snd.comp continuous_snd)).mul continuous_const
  have hr₂ : Continuous fun p : (α₁ × α₂ → Fin N → ℝ) × ℝ × ℝ × ℝ => p.2.2.2 * log 2 :=
    (continuous_snd.comp (continuous_snd.comp continuous_snd)).mul continuous_const
  have hT : IsClosed {p : (α₁ × α₂ → Fin N → ℝ) × ℝ × ℝ × ℝ |
      F₀ p.1 ≤ p.2.1 * log 2 ∧ F₁ p.1 ≤ p.2.2.1 * log 2 ∧ F₂ p.1 ≤ p.2.2.2 * log 2} :=
    (isClosed_le (hc₀.comp continuous_fst) hr₀).inter
      ((isClosed_le (hc₁.comp continuous_fst) hr₁).inter
        (isClosed_le (hc₂.comp continuous_fst) hr₂))
  have h := isClosed_exists_mem_compact (isCompact_setOf_isChannel (α := α₁ × α₂) (β := Fin N)) hT
  convert h using 1
  ext R
  simp only [gwSet, Set.mem_ofPred_eq]
  refine exists_congr fun κ => ?_
  constructor
  · rintro ⟨hκ, a0, a1, a2⟩
    have hμ := jointOf_isPMF hP hκ
    rw [gwInfo, mutualInfo_eq_add_sub hμ] at a0
    rw [gwCond₁, condEntropy_eq_sub hμ] at a1
    rw [gwCond₂, condEntropy_eq_sub hμ] at a2
    exact ⟨hκ, a0, a1, a2⟩
  · rintro ⟨hκ, a0, a1, a2⟩
    have hκ' : IsChannel κ := hκ
    have hμ := jointOf_isPMF hP hκ'
    refine ⟨hκ', ?_, ?_, ?_⟩
    · rwa [gwInfo, mutualInfo_eq_add_sub hμ]
    · rwa [gwCond₁, condEntropy_eq_sub hμ]
    · rwa [gwCond₂, condEntropy_eq_sub hμ]

/-- **The direct part of Theorem 3 of Lecture 15, for the closure.** For `V` on any finite set, the
rate triples with `R₀ ≥ I(U₁, U₂; V)`, `R₁ ≥ H(U₁|V)` and `R₂ ≥ H(U₂|V)` are in the region. -/
theorem mem_gwRegion_of_channel {υ : Type*} [Fintype υ] {κ : α₁ × α₂ → υ → ℝ} (hP : IsPMF P)
    (hκ : IsChannel κ) {R₀ R₁ R₂ : ℝ} (h₀ : gwInfo P κ ≤ R₀ * log 2)
    (h₁ : gwCond₁ P κ ≤ R₁ * log 2) (h₂ : gwCond₂ P κ ≤ R₂ * log 2) :
    (R₀, R₁, R₂) ∈ gwRegion P := by
  have hl := log_pos one_lt_two
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hj : ∀ R : ℝ, Tendsto (fun k : ℕ => R + 1 / ((k : ℝ) + 1)) atTop (𝓝 R) := fun R => by
    simpa using tendsto_const_nhds.add h0
  refine mem_closure_of_tendsto ((hj R₀).prodMk_nhds ((hj R₁).prodMk_nhds (hj R₂)))
    (Eventually.of_forall fun k => ?_)
  have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  have hpl := mul_pos hp hl
  refine isAchievableGW_of_lt hP hκ ?_ ?_ ?_
  · simp only [add_mul]
    linarith
  · simp only [add_mul]
    linarith
  · simp only [add_mul]
    linarith

/-- **The converse of Theorem 3 of Lecture 15, page 15-23.** A rate triple of the region satisfies
the bounds for some `V` with `|𝒰₁| |𝒰₂| + 4` values. -/
theorem gwRegion_subset_gwSet (hP : IsPMF P) :
    gwRegion P ⊆ gwSet P (Fintype.card (α₁ × α₂) + 4) := by
  have hl := log_pos one_lt_two
  have hclosed := isClosed_gwSet hP (Fintype.card (α₁ × α₂) + 4)
  refine closure_minimal ?_ hclosed
  rintro ⟨R₀, R₁, R₂⟩ ⟨hR₀, hR₁, hR₂, c, hc⟩
  -- The bound with a margin.
  have hτ : ∀ τ > 0, (R₀, R₁ + τ, R₂ + τ) ∈ gwSet P (Fintype.card (α₁ × α₂) + 4) := fun τ hτ => by
    have hτl : 0 < τ * log 2 := mul_pos hτ hl
    have hlim : Tendsto (fun n : ℕ => log 2 / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hL : 0 ≤ log (Fintype.card α₁) + log (Fintype.card α₂) := by positivity
    have hE : Tendsto (fun n => (c n).errProb P * (log (Fintype.card α₁) +
        log (Fintype.card α₂))) atTop (𝓝 0) := by
      simpa using hc.mul_const (log (Fintype.card α₁) + log (Fintype.card α₂))
    obtain ⟨n, hn1, hn2, hn⟩ := (((tendsto_order.1 hlim).2 _ (half_pos hτl)).and
      (((tendsto_order.1 hE).2 _ (half_pos hτl)).and (eventually_gt_atTop 0))).exists
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨k, κ, hκ, a0, a1, a2⟩ := (c n).exists_channel hP hn
    obtain ⟨κ', hκ', e0, e1, e2⟩ := exists_gw_reduce hP hκ (N := Fintype.card (α₁ × α₂) + 4) rfl
    have hdiv : log 2 = (log 2 / n) * n := (div_mul_cancel₀ _ hn'.ne').symm
    have he0 := GWCode.errProb_nonneg hP (c n)
    have hL₁ : 0 ≤ log (Fintype.card α₁) := log_natCast_nonneg _
    have hL₂ : 0 ≤ log (Fintype.card α₂) := log_natCast_nonneg _
    have hb₁ : (c n).errProb P * log (Fintype.card α₁) ≤ (c n).errProb P *
        (log (Fintype.card α₁) + log (Fintype.card α₂)) :=
      mul_le_mul_of_nonneg_left (by linarith) he0
    have hb₂ : (c n).errProb P * log (Fintype.card α₂) ≤ (c n).errProb P *
        (log (Fintype.card α₁) + log (Fintype.card α₂)) :=
      mul_le_mul_of_nonneg_left (by linarith) he0
    refine ⟨κ', hκ', ?_, ?_, ?_⟩
    · rw [e0]
      refine le_of_mul_le_mul_left (a0.trans ?_) hn'
      exact log_two_pow_floor_le n hR₀
    · rw [e1]
      refine le_of_mul_le_mul_left (a1.trans ?_) hn'
      have := log_two_pow_floor_le n hR₁
      have e : (c n).errProb P * (n * log (Fintype.card α₁)) =
          n * ((c n).errProb P * log (Fintype.card α₁)) := by ring
      rw [e]
      change _ ≤ (n : ℝ) * ((R₁ + τ) * log 2)
      rw [add_mul, mul_add]
      nlinarith
    · rw [e2]
      refine le_of_mul_le_mul_left (a2.trans ?_) hn'
      have := log_two_pow_floor_le n hR₂
      have e : (c n).errProb P * (n * log (Fintype.card α₂)) =
          n * ((c n).errProb P * log (Fintype.card α₂)) := by ring
      rw [e]
      change _ ≤ (n : ℝ) * ((R₂ + τ) * log 2)
      rw [add_mul, mul_add]
      nlinarith
  -- The limit.
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hj : ∀ R : ℝ, Tendsto (fun k : ℕ => R + 1 / ((k : ℝ) + 1)) atTop (𝓝 R) := fun R => by
    simpa using tendsto_const_nhds.add h0
  exact hclosed.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds ((hj R₁).prodMk_nhds (hj R₂)))
    (Eventually.of_forall fun k => hτ _ (by positivity))

/-- **Theorem 3 of Lecture 15 of [elgamal2010], page 15-22: the Gray–Wyner theorem.** The optimal
rate region is the set of the rate triples with `R₀ ≥ I(U₁, U₂; V)`, `R₁ ≥ H(U₁|V)` and
`R₂ ≥ H(U₂|V)` for some `p(v|u₁, u₂)`, where `V` has `|𝒰₁| |𝒰₂| + 4` values. -/
theorem gwRegion_eq (hP : IsPMF P) : gwRegion P = gwSet P (Fintype.card (α₁ × α₂) + 4) := by
  refine Set.Subset.antisymm (gwRegion_subset_gwSet hP) ?_
  rintro ⟨R₀, R₁, R₂⟩ ⟨κ, hκ, a0, a1, a2⟩
  exact mem_gwRegion_of_channel hP hκ a0 a1 a2

end Theorem

end InfoTheory
