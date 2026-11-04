/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCMarton
public import InfoTheoryLib.Network.BCTimeSharing
public import InfoTheoryLib.Network.ICBounds
public import InfoTheoryLib.RateDistortion.Basic
public import InfoTheoryLib.StateChannel.Compound

/-!
# Deterministic broadcast channels

Every achievable rate pair of a DM-BC satisfies `R₁ ≤ I(X; Y₁)`, `R₂ ≤ I(X; Y₂)` and
`R₁ + R₂ ≤ I(X; Y₁, Y₂)` for some `p(x)`, by Fano's inequality and the concavity of the mutual
information in `p(x)`. For the deterministic DM-BC, with `Y₁ = y₁(X)` and `Y₂ = y₂(X)`, these bounds
are `R₁ ≤ H(Y₁)`, `R₂ ≤ H(Y₂)`, `R₁ + R₂ ≤ H(Y₁, Y₂)`, and Marton's inner bound with `U₁ = Y₁`,
`U₂ = Y₂` shows that they give the capacity region.

## Main definitions

* `bcCutSetRegionBits W`: the rate pairs with these three bounds, in bits.
* `IsDeterministicBC W`: `Y₁ = y₁(X)` and `Y₂ = y₂(X)`.

## Main statements

* `IsAchievableBCBits.mem_closure_bcCutSetRegionBits`: the outer bound, for every DM-BC.
* `bcCapacityRegionBits_eq_of_isDeterministicBC`: **the capacity region of the deterministic
  DM-BC (Lecture 9)**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 9
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β₁ β₂ : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

/-! ### Fano's inequality for a function of the messages -/

section Fano

variable {𝒲 𝓜 β' : Type*} [Fintype 𝒲] [Fintype 𝓜] [Fintype β'] [Nonempty 𝒲] {n : ℕ}

open Classical in
/-- A message `m(W)`, function of a uniformly distributed `W`, decoded from `n` uses of the channel
`V` with the inputs `x(W)`, satisfies
`log |𝓜| ≤ ∑ᵢ I(Xᵢ; Yᵢ) + log 2 + Pₑ log |𝓜|`, if `m(W)` is uniformly distributed. -/
theorem log_le_sum_mutualInfoOf_of_dec [Nonempty α] (x : 𝒲 → Fin n → α) {V : α → β' → ℝ}
    (hV : IsChannel V) (m : 𝒲 → 𝓜) (hm : dist (uniformPMF 𝒲) m = uniformPMF 𝓜) [Nonempty 𝓜]
    (g : (Fin n → β') → 𝓜) {e : ℝ}
    (he : e = (∑ w, ∑ y, if g y ≠ m w then channelExt V n (x w) y else 0) / Fintype.card 𝒲) :
    log (Fintype.card 𝓜) ≤ ∑ i, mutualInfoOf (dist (uniformPMF 𝒲) fun w => x w i) V + log 2 +
      e * log (Fintype.card 𝓜) := by
  have hν : IsPMF (uniformPMF 𝒲) := uniformPMF_isPMF
  set μ := fbLaw (uniformPMF 𝒲) V (nfEnc x) n
  have hμ : IsPMF μ := fbLaw_isPMF hν hV n
  set Mv : 𝒲 × (Fin n → β') → 𝓜 := fun z => m z.1
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ Mv Prod.snd
  have h2 := fano_weak hμ Mv Prod.snd g
  have h3 : I[Mv : Prod.snd ; μ] ≤ I[Prod.fst : Prod.snd ; μ] := by
    rw [mutualInfo_comm hμ Mv, mutualInfo_comm hμ Prod.fst]
    exact mutualInfo_comp_le hμ Prod.snd Prod.fst m
  have h4 := mutualInfo_fbLaw_nfEnc_le hν hV x n le_rfl
  have hH : H[Mv ; μ] = log (Fintype.card 𝓜) := by
    have e : Mv = m ∘ Prod.fst := rfl
    rw [entropyRV, e, dist_comp_eq, dist_fst_fbLaw hV, hm, entropy_uniformPMF]
  have herr : errProb μ Mv Prod.snd g =
      (∑ w, ∑ y, if g y ≠ m w then channelExt V n (x w) y else 0) / Fintype.card 𝒲 := by
    simp only [errProb, Fintype.sum_prod_type, Mv, μ, fbLaw_nfEnc, uniformPMF]
    rw [sum_div]
    refine sum_congr rfl fun w _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  rw [herr, ← he] at h2
  have h5 : ∑ i : Fin n, mutualInfoOf (dist (uniformPMF 𝒲) fun w => x w (Fin.castLE le_rfl i)) V =
      ∑ i, mutualInfoOf (dist (uniformPMF 𝒲) fun w => x w i) V := rfl
  linarith

end Fano

/-! ### The outer bound -/

/-- The rate pairs with `R₁ ≤ I(X; Y₁)`, `R₂ ≤ I(X; Y₂)` and `R₁ + R₂ ≤ I(X; Y₁, Y₂)` for some
`p(x)`, in bits. -/
def bcCutSetRegionBits (W : α → β₁ × β₂ → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ p : α → ℝ, IsPMF p ∧ R.1 ≤ mutualInfoOf p (bcMarg₁ W) / log 2 ∧
    R.2 ≤ mutualInfoOf p (bcMarg₂ W) / log 2 ∧ R.1 + R.2 ≤ mutualInfoOf p W / log 2}

/-- The first message of a uniform pair is uniform. -/
lemma dist_uniformPMF_prod_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    dist (uniformPMF (A × B)) Prod.fst = uniformPMF A := by
  funext a
  rw [dist_fst]
  simp only [uniformPMF, Fintype.card_prod, sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul]
  have h : (Fintype.card B : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The second message of a uniform pair is uniform. -/
lemma dist_uniformPMF_prod_snd {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    dist (uniformPMF (A × B)) Prod.snd = uniformPMF B := by
  funext b
  rw [dist_snd]
  simp only [uniformPMF, Fintype.card_prod, sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul]
  have h : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- **An outer bound for the DM-BC.** Every achievable rate pair has `R₁ ≤ I(X; Y₁)`,
`R₂ ≤ I(X; Y₂)` and `R₁ + R₂ ≤ I(X; Y₁, Y₂)`, up to closure, with the same `p(x)`. -/
theorem IsAchievableBCBits.mem_closure_bcCutSetRegionBits [Nonempty α] (hW : IsChannel W)
    {R₁ R₂ : ℝ} (h : IsAchievableBCBits W R₁ R₂) : (R₁, R₂) ∈ closure (bcCutSetRegionBits W) := by
  classical
  obtain ⟨c, hc⟩ := h
  have hl := log_pos one_lt_two
  set P : ℕ → ℝ := fun n => (c n).errProb W with hPd
  have hP₁ : ∀ n, (c n).errProb₁ W ≤ P n := fun n =>
    (le_max_left _ _).trans ((c n).max_errProb_le hW)
  have hP₂ : ∀ n, (c n).errProb₂ W ≤ P n := fun n =>
    (le_max_right _ _).trans ((c n).max_errProb_le hW)
  have hP0 : ∀ n, 0 ≤ P n := fun n => ((c n).errProb₁_nonneg hW).trans (hP₁ n)
  refine mem_closure_of_sub_icEps (tendsto_icEps (R₁ := R₁) (R₂ := R₂) hP0 hc) fun n hn => ?_
  have hnm₁ : 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := by positivity
  have hnm₂ : 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := by positivity
  set M₁ := 2 ^ ⌈(n : ℝ) * R₁⌉₊
  set M₂ := 2 ^ ⌈(n : ℝ) * R₂⌉₊
  have : Nonempty (Fin M₁) := ⟨⟨0, hnm₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hnm₂⟩⟩
  set x := (c n).enc
  set A := log ((M₁ : ℕ) : ℝ)
  set B := log ((M₂ : ℕ) : ℝ)
  have hA : 0 ≤ A := log_natCast_nonneg _
  have hB : 0 ≤ B := log_natCast_nonneg _
  have hAb := (log_two_pow_ceil_bounds n R₁).1
  have hBb := (log_two_pow_ceil_bounds n R₂).1
  have hcard : ((Fintype.card (Fin M₁ × Fin M₂) : ℕ) : ℝ) = M₁ * M₂ := by simp
  -- Receiver 1.
  have b₁ := log_le_sum_mutualInfoOf_of_dec x hW.bcMarg₁ Prod.fst
    dist_uniformPMF_prod_fst (c n).dec₁ (e := (c n).errProb₁ W) (by
      rw [hcard]
      simp only [BCCode.errProb₁]
      congr!)
  rw [Fintype.card_fin] at b₁
  -- Receiver 2.
  have b₂ := log_le_sum_mutualInfoOf_of_dec x hW.bcMarg₂ Prod.snd
    dist_uniformPMF_prod_snd (c n).dec₂ (e := (c n).errProb₂ W) (by
      rw [hcard]
      simp only [BCCode.errProb₂]
      congr!)
  rw [Fintype.card_fin] at b₂
  -- Both receivers.
  have b₁₂ := log_le_sum_mutualInfoOf_of_dec x hW (id : Fin M₁ × Fin M₂ → Fin M₁ × Fin M₂)
    (dist_id _) (fun y => ((c n).dec₁ fun i => (y i).1, (c n).dec₂ fun i => (y i).2))
    (e := (c n).errProb W) (by
      rw [hcard]
      simp only [BCCode.errProb, id, ne_eq, Prod.ext_iff, not_and_or]
      congr!)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul,
    log_mul (by exact_mod_cast hnm₁.ne') (by exact_mod_cast hnm₂.ne')] at b₁₂
  -- A single input distribution.
  set p : Fin n → α → ℝ := fun i => dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => x w i
  have hp : ∀ i, IsPMF (p i) := fun i => uniformPMF_isPMF.dist _
  have hb1 := mutualInfoOf_sum_le (W := fun _ : Unit => bcMarg₁ W) (fun _ => hW.bcMarg₁) hn hp ()
  have hb2 := mutualInfoOf_sum_le (W := fun _ : Unit => bcMarg₂ W) (fun _ => hW.bcMarg₂) hn hp ()
  have hb3 := mutualInfoOf_sum_le (W := fun _ : Unit => W) (fun _ => hW) hn hp ()
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hε := icEps_nonneg (R₁ := R₁) (R₂ := R₂) hP0 n
  have hdiv : ∀ {S I : ℝ}, S ≤ n * I → (1 / (n : ℝ) * S) / log 2 ≤ I / log 2 := fun {S I} h => by
    refine div_le_div_of_nonneg_right ?_ hl.le
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hn']
    linarith
  have hPA := mul_le_mul_of_nonneg_right (hP₁ n) hA
  have hPB := mul_le_mul_of_nonneg_right (hP₂ n) hB
  have hP0A := mul_nonneg (hP0 n) hA
  have hP0B := mul_nonneg (hP0 n) hB
  refine ⟨_, hb1.1, ?_, ?_, ?_⟩
  · refine (sub_icEps_le hn ?_).trans (hdiv hb1.2)
    nlinarith
  · refine (sub_icEps_le hn ?_).trans (hdiv hb2.2)
    nlinarith
  · have hs := sub_icEps_le (a := R₁ + R₂) (S := ∑ i, mutualInfoOf (p i) W) (R₁ := R₁) (R₂ := R₂)
      (P := P) hn (by nlinarith)
    refine le_trans ?_ (hs.trans (hdiv hb3.2))
    linarith

/-! ### Deterministic channels -/

section Deterministic

variable {𝒵 𝒰 : Type*} [Fintype 𝒵] [Fintype 𝒰]

/-- If the output of the channel is `U = f(Z)`, then `I(U; Y) = H(U)`. -/
lemma mutualInfo_comp_jointOf_of_output_eq {q : 𝒵 → ℝ} (hq : IsPMF q) {K : 𝒵 → 𝒰 → ℝ}
    (hK : IsChannel K) (f : 𝒵 → 𝒰) (hsupp : ∀ z y, q z ≠ 0 → K z y ≠ 0 → y = f z) :
    I[fun w : 𝒵 × 𝒰 => f w.1 : Prod.snd ; jointOf q K] = entropy (dist q f) := by
  classical
  have hJ := jointOf_isPMF hq hK
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hJ (fun w : 𝒵 × 𝒰 => f w.1) Prod.snd
  have h0 : H[fun w : 𝒵 × 𝒰 => f w.1 | Prod.snd ; jointOf q K] = 0 := by
    have e : H[fun w : 𝒵 × 𝒰 => f w.1 | Prod.snd ; jointOf q K] =
        H[Prod.snd | Prod.snd ; jointOf q K] := by
      refine condEntropy_eq_of_dist_pair_eq hJ hJ ?_
      funext a
      simp only [dist]
      refine sum_congr rfl fun w _ => ?_
      by_cases hw : jointOf q K w = 0
      · simp [hw]
      · have hqw : q w.1 ≠ 0 := fun h => hw (by simp [jointOf, h])
        have hKw : K w.1 w.2 ≠ 0 := fun h => hw (by simp [jointOf, h])
        simp only [pair, hsupp _ _ hqw hKw]
    rw [e]
    exact condEntropy_comp_self hJ Prod.snd id
  have h2 : H[fun w : 𝒵 × 𝒰 => f w.1 ; jointOf q K] = entropy (dist q f) := by
    have e : (fun w : 𝒵 × 𝒰 => f w.1) = f ∘ Prod.fst := rfl
    rw [entropyRV, e, dist_comp_eq, dist_jointOf_fst hK]
  rw [h1, h0, h2, sub_zero]

/-- For a deterministic channel, `I(X; Y) = H(f(X))`. -/
lemma mutualInfoOf_detChannel {α' β' : Type*} [Fintype α'] [Fintype β'] {p : α' → ℝ} (hp : IsPMF p)
    (f : α' → β') : mutualInfoOf p (detChannel f) = entropy (dist p f) := by
  classical
  have hzero : ∀ x, entropy (detChannel f x) = 0 := fun x => by
    rw [entropy_eq_sum_negMulLog]
    refine sum_eq_zero fun y _ => ?_
    simp only [detChannel]
    split_ifs <;> simp
  rw [mutualInfoOf_eq hp (detChannel_isChannel f)]
  simp only [hzero, mul_zero, sum_const_zero, sub_zero]
  congr 1
  funext y
  simp only [outDist, detChannel, dist, mul_ite, mul_one, mul_zero]

open Classical in
/-- **Lecture 9 of [elgamal2010], page 9-21.** The deterministic DM-BC: `Y₁ = y₁(X)`,
`Y₂ = y₂(X)`. -/
def IsDeterministicBC (W : α → β₁ × β₂ → ℝ) : Prop :=
  ∃ (f₁ : α → β₁) (f₂ : α → β₂), W = detChannel fun x => (f₁ x, f₂ x)

omit [Fintype α] [Fintype β₁] in
lemma bcMarg₁_det (f₁ : α → β₁) (f₂ : α → β₂) :
    bcMarg₁ (detChannel fun x => (f₁ x, f₂ x)) = detChannel f₁ := by
  classical
  funext x y₁
  simp only [bcMarg₁, detChannel, Prod.mk.injEq, ite_and]
  by_cases h : y₁ = f₁ x <;> simp [h]

omit [Fintype α] [Fintype β₂] in
lemma bcMarg₂_det (f₁ : α → β₁) (f₂ : α → β₂) :
    bcMarg₂ (detChannel fun x => (f₁ x, f₂ x)) = detChannel f₂ := by
  classical
  funext x y₂
  simp only [bcMarg₂, detChannel, Prod.mk.injEq, ite_and]
  rw [sum_ite_eq univ (f₁ x)]
  simp

/-- **Marton's inner bound for the deterministic DM-BC**, with `U₁ = Y₁`, `U₂ = Y₂`: a pair of
nonnegative rates is achievable if `R₁ < H(Y₁)`, `R₂ < H(Y₂)`, `R₁ + R₂ < H(Y₁, Y₂)`. -/
theorem isAchievableBCBits_of_det [Nonempty α] (f₁ : α → β₁) (f₂ : α → β₂) {p : α → ℝ}
    (hp : IsPMF p) {R₁ R₂ : ℝ} (h₁ : 0 ≤ R₁) (h₂ : 0 ≤ R₂)
    (h1 : R₁ * log 2 < entropy (dist p f₁)) (h2 : R₂ * log 2 < entropy (dist p f₂))
    (h12 : (R₁ + R₂) * log 2 < entropy (dist p fun x => (f₁ x, f₂ x))) :
    IsAchievableBCBits (detChannel fun x => (f₁ x, f₂ x)) R₁ R₂ := by
  classical
  set W : α → β₁ × β₂ → ℝ := detChannel fun x => (f₁ x, f₂ x)
  have hW : IsChannel W := detChannel_isChannel _
  set g : α → β₁ × β₂ := fun x => (f₁ x, f₂ x)
  set q := dist p g
  have hq : IsPMF q := hp.dist g
  obtain ⟨x₀⟩ := ‹Nonempty α›
  set x : β₁ × β₂ → α := fun u => if h : ∃ a, g a = u then h.choose else x₀
  have hx : ∀ u, q u ≠ 0 → g (x u) = u := fun u hu => by
    have hex : ∃ a, g a = u := by
      by_contra hne
      refine hu ?_
      simp only [q, dist]
      refine sum_eq_zero fun a _ => ?_
      split_ifs with h
      · exact absurd ⟨a, h⟩ hne
      · rfl
    simp only [x, hex, dite_true]
    exact hex.choose_spec
  have hK₁ := martonK₁_isChannel hW x
  have hK₂ := martonK₂_isChannel hW x
  have hI₁ : martonInfo₁ q x W = entropy (dist q Prod.fst) := by
    refine mutualInfo_comp_jointOf_of_output_eq hq hK₁ Prod.fst fun z y hz hy => ?_
    simp only [martonK₁, W, bcMarg₁_det, detChannel] at hy
    have : y = f₁ (x z) := by
      by_contra h
      refine hy ?_
      split_ifs with h'
      · exact absurd h'.symm h
      · rfl
    rw [this]
    exact congrArg Prod.fst (hx z hz)
  have hI₂ : martonInfo₂ q x W = entropy (dist q Prod.snd) := by
    refine mutualInfo_comp_jointOf_of_output_eq hq hK₂ Prod.snd fun z y hz hy => ?_
    simp only [martonK₂, W, bcMarg₂_det, detChannel] at hy
    have : y = f₂ (x z) := by
      by_contra h
      refine hy ?_
      split_ifs with h'
      · exact absurd h'.symm h
      · rfl
    rw [this]
    exact congrArg Prod.snd (hx z hz)
  have hd₁ : dist q Prod.fst = dist p f₁ := by
    rw [← dist_comp_eq]
    rfl
  have hd₂ : dist q Prod.snd = dist p f₂ := by
    rw [← dist_comp_eq]
    rfl
  have hI₁₂ : martonInfo₁ q x W + martonInfo₂ q x W - martonInfo₁₂ q = entropy q := by
    have h := mutualInfo_eq_add_sub hq (Prod.fst : β₁ × β₂ → β₁) Prod.snd
    have e : H[pair Prod.fst Prod.snd ; q] = entropy q := by
      rw [entropyRV, dist_pair_fst_snd]
    rw [hI₁, hI₂, martonInfo₁₂, h, e]
    simp only [entropyRV]
    ring
  refine isAchievableBCBits_of_marton hq hW x h₁ h₂ ?_ ?_ ?_
  · rw [hI₁, hd₁]
    exact h1
  · rw [hI₂, hd₂]
    exact h2
  · rw [hI₁₂]
    exact h12

/-- A rate below the capacity of `p(y₂ | x)` is achievable with a single message for receiver 1. -/
theorem isAchievableBCBits_of_lt_capacity₂ [Nonempty α] (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h₁ : R₁ ≤ 0) (h₂ : R₂ < capacity (bcMarg₂ W) / log 2) : IsAchievableBCBits W R₁ R₂ := by
  obtain ⟨c, hc⟩ := isAchievableRateAvg_of_lt hW.bcMarg₂ h₂
  have hM : ∀ n : ℕ, 2 ^ ⌈n * R₁⌉₊ = 1 := fun n => by
    rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) h₁), pow_zero]
  refine ⟨fun n => BCCode.ofReceiver₂Code (c n) (hM n), ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => superposition_errProb_nonneg hW _) fun n => ?_
  refine ((BCCode.ofReceiver₂Code (β₁ := β₁) (c n) (hM n)).errProb_le_add hW).trans ?_
  rw [BCCode.errProb₁_eq_zero _ (hM n), zero_add]
  rw [BCCode.errProb₂_eq_avgErrProb _ _ (by positivity) (by positivity) rfl fun _ => rfl]

/-- A rate below the capacity of `p(y₁ | x)` is achievable with a single message for receiver 2. -/
theorem isAchievableBCBits_of_lt_capacity₁ [Nonempty α] (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h₂ : R₂ ≤ 0) (h₁ : R₁ < capacity (bcMarg₁ W) / log 2) : IsAchievableBCBits W R₁ R₂ := by
  obtain ⟨c, hc⟩ := isAchievableRateAvg_of_lt hW.bcMarg₁ h₁
  have hM : ∀ n : ℕ, 2 ^ ⌈n * R₂⌉₊ = 1 := fun n => by
    rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) h₂), pow_zero]
  refine ⟨fun n => BCCode.ofReceiver₁Code (c n) (hM n), ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
    (fun n => superposition_errProb_nonneg hW _) fun n => ?_
  refine ((BCCode.ofReceiver₁Code (β₂ := β₂) (c n) (hM n)).errProb_le_add hW).trans ?_
  rw [BCCode.errProb₂_eq_zero _ (hM n), add_zero]
  rw [BCCode.errProb₁_eq_avgErrProb _ _ (by positivity) (by positivity) rfl fun _ => rfl]

/-- **Lecture 9 of [elgamal2010], page 9-21.** The capacity region of the deterministic DM-BC is the
set of rate pairs with `R₁ ≤ H(Y₁)`, `R₂ ≤ H(Y₂)`, `R₁ + R₂ ≤ H(Y₁, Y₂)` for some `p(x)`, in bits,
up to closure. -/
theorem bcCapacityRegionBits_eq_of_isDeterministicBC [Nonempty α] (hW : IsChannel W)
    (h : IsDeterministicBC W) : bcCapacityRegionBits W = closure (bcCutSetRegionBits W) := by
  obtain ⟨f₁, f₂, rfl⟩ := h
  have hl := log_pos one_lt_two
  refine Set.Subset.antisymm (closure_minimal (fun R hR => ?_) isClosed_closure)
    (closure_minimal ?_ isClosed_closure)
  · exact IsAchievableBCBits.mem_closure_bcCutSetRegionBits hW hR
  · rintro ⟨R₁, R₂⟩ ⟨p, hp, h₁, h₂, h₁₂⟩
    dsimp only at h₁ h₂ h₁₂
    rw [bcMarg₁_det, mutualInfoOf_detChannel hp, le_div_iff₀ hl] at h₁
    rw [bcMarg₂_det, mutualInfoOf_detChannel hp, le_div_iff₀ hl] at h₂
    rw [mutualInfoOf_detChannel hp, le_div_iff₀ hl] at h₁₂
    have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine mem_closure_of_sub_icEps hε fun n _ => ?_
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    set t := 1 / ((n : ℝ) + 1)
    have htl : 0 < t * log 2 := mul_pos hpos hl
    have a₁ : (R₁ - t) * log 2 < entropy (dist p f₁) := by nlinarith
    have a₂ : (R₂ - t) * log 2 < entropy (dist p f₂) := by nlinarith
    have a₁₂ : (R₁ - t + (R₂ - t)) * log 2 < entropy (dist p fun x => (f₁ x, f₂ x)) := by nlinarith
    rcases le_or_gt (R₁ - t) 0 with hR₁ | hR₁
    · refine isAchievableBCBits_of_lt_capacity₂ hW hR₁ ?_
      rw [lt_div_iff₀ hl]
      refine a₂.trans_le ?_
      have := mutualInfoOf_le_capacity hp hW.bcMarg₂
      rwa [bcMarg₂_det, mutualInfoOf_detChannel hp, ← bcMarg₂_det f₁] at this
    rcases le_or_gt (R₂ - t) 0 with hR₂ | hR₂
    · refine isAchievableBCBits_of_lt_capacity₁ hW hR₂ ?_
      rw [lt_div_iff₀ hl]
      refine a₁.trans_le ?_
      have := mutualInfoOf_le_capacity hp hW.bcMarg₁
      rwa [bcMarg₁_det, mutualInfoOf_detChannel hp, ← bcMarg₁_det f₁ f₂] at this
    exact isAchievableBCBits_of_det f₁ f₂ hp hR₁.le hR₂.le a₁ a₂ a₁₂

end Deterministic

end InfoTheory
