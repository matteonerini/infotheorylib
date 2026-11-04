/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Achievability
public import InfoTheoryLib.Entropy.Fano
public import InfoTheoryLib.MutualInformation.Conditional
public import InfoTheoryLib.StochasticProcess.Basic

/-!
# The converse to the channel coding theorem, and feedback

No code can send information reliably at a rate above capacity. The key bound is
`I(W; Yⁿ) ≤ nC` between a message `W` and the `n` outputs of a memoryless channel. We prove it
once for feedback codes, where the input `Xₖ₊₁ = fₖ(W, Y₁, …, Yₖ)` may depend on the past outputs:
`I(W; Yₖ₊₁ | Yᵏ) ≤ H(Yₖ₊₁) - H(Yₖ₊₁ | W, Yᵏ) = I(Xₖ₊₁; Yₖ₊₁) ≤ C`, (7.125)–(7.132). Codes without
feedback, where `Xₖ₊₁` depends only on `W`, are a special case. Combined with Fano's inequality,
the bound gives the converse, (7.98)–(7.105). It also gives zero-error codes (7.82)–(7.87),
Lemma 7.9.2, and the fact that feedback does not increase capacity (Theorem 7.12.1).

The message `W` takes values in a finite set `𝒲` with prior `ν`. For codes it is uniform on
`{0, …, M - 1}`. A (feedback) encoder is `enc : ∀ k, 𝒲 → (Fin k → β) → α`, the input at time
`k + 1` given the message and the first `k` outputs. Logarithms are natural.

## Main definitions

* `fbLaw ν W enc k`: the joint law of the message and the first `k` channel outputs.
* `nfEnc x`: the encoder without feedback sending the codeword `x(w)`.
* `FeedbackCode M n α β`, `FeedbackCode.errProb`, `IsAchievableRateFB`, `fbCapacity`: feedback
  codes, their probability of error (7.119), and the capacity with feedback.

## Main statements

* `mutualInfo_fbLaw_le`: `I(W; Yⁿ) ≤ nC`, (7.125)–(7.132).
* `mutualInfo_channelExt_le`: Lemma 7.9.2, `I(Xⁿ; Yⁿ) ≤ nC` for every input distribution.
* `ChannelCode.condEntropy_message_le`: Lemma 7.9.1 (Fano's inequality for codes),
  `H(W | Ŵ) ≤ log 2 + Pₑ^(n) log M` for the estimate `Ŵ = g(Yⁿ)`.
* `ChannelCode.one_sub_avgErrProb_mul_log_le`: (7.98)–(7.102),
  `(1 - Pₑ^(n)) log M ≤ log 2 + nC`.
* `ChannelCode.log_le_of_avgErrProb_eq_zero`: (7.82)–(7.87), a zero-error code has `log M ≤ nC`.
* `ChannelCode.avgErrProb_ge`: (7.105), `Pₑ^(n) ≥ 1 - C/R - log 2/(nR)`.
* `IsAchievableRate.le_capacity`: Theorem 7.7.1 (converse), achievable rates are at most `C`.
* `opCapacity_eq_capacity`: Theorem 7.7.1, the operational capacity is the information capacity.
* `fbCapacity_eq_capacity`: Theorem 7.12.1, `C_FB = C`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 7.8–7.12
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ### Mutual information with the same joint law -/

section General

variable {Ω Ω' γ δ : Type*} [Fintype Ω] [Fintype Ω'] [Fintype γ] [Fintype δ]

/-- `H(f(X) | Y) ≤ H(X | Y)`. -/
lemma condEntropy_comp_le {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → γ) (Y : Ω → δ) {ε : Type*}
    [Fintype ε] (f : γ → ε) : H[f ∘ X | Y ; μ] ≤ H[X | Y ; μ] := by
  have h1 := chain_rule_cond hμ X (f ∘ X) Y
  have h0 : H[f ∘ X | pair X Y ; μ] = 0 :=
    condEntropy_comp_self hμ (pair X Y) fun z => f z.1
  have h2 := chain_rule_cond hμ (f ∘ X) X Y
  have hswap : H[pair X (f ∘ X) | Y ; μ] = H[pair (f ∘ X) X | Y ; μ] :=
    condEntropy_congr_left hμ Y Prod.swap Prod.swap_injective fun _ => rfl
  have := condEntropy_nonneg hμ X (pair (f ∘ X) Y)
  linarith

/-! ### A channel acting on a conditional input -/

variable {μ : Ω → ℝ} {Z : Ω → γ} {Y : Ω → β} {W : α → β → ℝ} (f : γ → α)

/-- Group a sum over the values of `Z` by the values of `f(Z)`. -/
lemma sum_dist_mul_comp (μ : Ω → ℝ) (Z : Ω → γ) (g : α → ℝ) :
    ∑ z, dist μ Z z * g (f z) = ∑ x, dist μ (f ∘ Z) x * g x := by
  rw [sum_dist_mul, sum_dist_mul]
  rfl

include f in
/-- If, given `Z = z`, the output `Y` is produced by the channel `W` from the input `f(z)`, then
`H(Y | Z) = ∑ₓ Pr{f(Z) = x} H(W(· | x))`. -/
lemma condEntropy_of_channel
    (h : ∀ z y, dist μ (pair Z Y) (z, y) = dist μ Z z * W (f z) y) :
    H[Y | Z ; μ] = ∑ x, dist μ (f ∘ Z) x * entropy (W x) := by
  rw [← sum_dist_mul_comp f μ Z fun x => entropy (W x), condEntropy]
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : dist μ Z z = 0
  · simp [hz]
  · congr 1
    unfold condEntropyAt
    congr 1
    funext y
    rw [condDist, h, mul_div_cancel_left₀ _ hz]

omit [Fintype β] [Fintype γ] in
include f in
/-- In the same situation, the law of `Y` is the output law of `W` for the input law of `f(Z)`. -/
lemma dist_of_channel [Finite γ]
    (h : ∀ z y, dist μ (pair Z Y) (z, y) = dist μ Z z * W (f z) y) :
    dist μ Y = outDist (dist μ (f ∘ Z)) W := by
  have := Fintype.ofFinite γ
  funext y
  rw [← sum_dist_pair_left μ Z Y y, outDist]
  simp only [h]
  exact sum_dist_mul_comp f μ Z fun x => W x y

/-- In the same situation, `H(Y) - H(Y | Z) = I(f(Z); Y)`. -/
lemma entropy_sub_condEntropy_eq_mutualInfoOf (hμ : IsPMF μ) (hW : IsChannel W)
    (h : ∀ z y, dist μ (pair Z Y) (z, y) = dist μ Z z * W (f z) y) :
    H[Y ; μ] - H[Y | Z ; μ] = mutualInfoOf (dist μ (f ∘ Z)) W := by
  rw [condEntropy_of_channel f h, entropyRV, dist_of_channel f h,
    ← mutualInfoOf_eq (hμ.dist (f ∘ Z)) hW]

include f in
/-- In the same situation, `H(Y) - H(Y | Z) = I(f(Z); Y) ≤ C`. -/
lemma entropy_sub_condEntropy_le_capacity (hμ : IsPMF μ) (hW : IsChannel W)
    (h : ∀ z y, dist μ (pair Z Y) (z, y) = dist μ Z z * W (f z) y) :
    H[Y ; μ] - H[Y | Z ; μ] ≤ capacity W := by
  rw [entropy_sub_condEntropy_eq_mutualInfoOf f hμ hW h]
  exact mutualInfoOf_le_capacity (hμ.dist (f ∘ Z)) hW

end General

/-! ### The joint law of a message and the channel outputs -/

variable {𝒲 : Type*} [Fintype 𝒲]

/-- The joint law of the message `W` (with prior `ν`) and the first `k` outputs of the channel
`W`, when the input at time `j + 1` is `enc j w (y₁, …, yⱼ)`. -/
def fbLaw (ν : 𝒲 → ℝ) (W : α → β → ℝ) (enc : ∀ k, 𝒲 → (Fin k → β) → α) :
    (k : ℕ) → 𝒲 × (Fin k → β) → ℝ
  | 0, z => ν z.1
  | k + 1, z => fbLaw ν W enc k (z.1, Fin.init z.2) *
      W (enc k z.1 (Fin.init z.2)) (z.2 (Fin.last k))

variable {ν : 𝒲 → ℝ} {W : α → β → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β) → α}

omit [Fintype α] [Fintype β] [Fintype 𝒲] in
lemma fbLaw_snoc (k : ℕ) (w : 𝒲) (u : Fin k → β) (b : β) :
    fbLaw ν W enc (k + 1) (w, Fin.snoc u b) = fbLaw ν W enc k (w, u) * W (enc k w u) b := by
  simp [fbLaw, Fin.init_snoc]

omit [Fintype α] in
lemma fbLaw_isPMF (hν : IsPMF ν) (hW : IsChannel W) (k : ℕ) : IsPMF (fbLaw ν W enc k) := by
  induction k with
  | zero =>
    refine ⟨fun z => hν.nonneg z.1, ?_⟩
    rw [Fintype.sum_prod_type]
    simp [fbLaw, hν.sum_eq_one]
  | succ k ih =>
    refine ⟨fun z => mul_nonneg (ih.nonneg _) ((hW _).nonneg _), ?_⟩
    rw [Fintype.sum_prod_type]
    simp_rw [sum_snoc k, fbLaw_snoc, ← mul_sum, (hW _).sum_eq_one, mul_one]
    rw [← Fintype.sum_prod_type]
    exact ih.sum_eq_one

omit [Fintype α] in
/-- The law of `(W, Y₁, …, Yₖ)` is the marginal of the law of `(W, Y₁, …, Yₖ₊₁)`. -/
lemma dist_fbLaw_init (hW : IsChannel W) (k : ℕ) :
    dist (fbLaw ν W enc (k + 1)) (fun z => (z.1, Fin.init z.2)) = fbLaw ν W enc k := by
  classical
  funext ⟨w, u⟩
  simp only [dist, Fintype.sum_prod_type]
  simp_rw [sum_snoc k, Fin.init_snoc, Prod.mk.injEq]
  rw [sum_eq_single w (fun w' _ hw' => by simp [hw']) (by simp)]
  rw [sum_eq_single u (fun u' _ hu' => by simp [hu']) (by simp)]
  simp [fbLaw_snoc, ← mul_sum, (hW _).sum_eq_one]

/-- **(7.125)–(7.131)** Each channel use increases the mutual information between the message and
the outputs by at most the mutual information between the input `Xₖ₊₁` and the output `Yₖ₊₁`:
`I(W; Yᵏ⁺¹) ≤ I(W; Yᵏ) + I(Xₖ₊₁; Yₖ₊₁)`. -/
theorem mutualInfo_fbLaw_succ_le_mutualInfoOf (hν : IsPMF ν) (hW : IsChannel W) (k : ℕ) :
    I[Prod.fst : Prod.snd ; fbLaw ν W enc (k + 1)] ≤
      I[Prod.fst : Prod.snd ; fbLaw ν W enc k] +
        mutualInfoOf (dist (fbLaw ν W enc (k + 1)) fun z => enc k z.1 (Fin.init z.2)) W := by
  classical
  set μ := fbLaw ν W enc (k + 1)
  have hμ : IsPMF μ := fbLaw_isPMF hν hW (k + 1)
  set Yp : 𝒲 × (Fin (k + 1) → β) → (Fin k → β) := fun z => Fin.init z.2
  set Yl : 𝒲 × (Fin (k + 1) → β) → β := fun z => z.2 (Fin.last k)
  set Wv : 𝒲 × (Fin (k + 1) → β) → 𝒲 := Prod.fst
  -- `Yᵏ⁺¹ = (Yᵏ, Yₖ₊₁)` and the chain rule.
  have h1 : I[Wv : Prod.snd ; μ] = I[Wv : pair Yl Yp ; μ] :=
    mutualInfo_congr_right hμ Wv (fun v : β × (Fin k → β) => (Fin.snoc v.2 v.1 : Fin (k + 1) → β))
      (fun a b hab => by
        have := snoc_injective2 (α := β) k (a₁ := (a.2, a.1)) (a₂ := (b.2, b.1)) hab
        simp only [Prod.mk.injEq] at this
        exact Prod.ext this.2 this.1)
      fun z => by simp [Yl, Yp, Fin.snoc_init_self]
  have h2 := chain_rule_mutualInfo₂ hμ Wv Yl Yp
  -- `I(W; Yᵏ)` is computed from the marginal law.
  have h3 : I[Wv : Yp ; μ] = I[Prod.fst : Prod.snd ; fbLaw ν W enc k] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    exact dist_fbLaw_init hW k
  -- `I(W; Yₖ₊₁ | Yᵏ) ≤ H(Yₖ₊₁) - H(Yₖ₊₁ | Yᵏ, W)`.
  have h4 : I[Wv : Yl | Yp ; μ] ≤ H[Yl ; μ] - H[Yl | pair Yp Wv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    linarith [condEntropy_le_entropy hμ Yl Yp]
  -- Given `(Yᵏ, W) = (u, w)`, `Yₖ₊₁` is the output of the channel for the input `enc k w u`.
  have hchan : ∀ (z : (Fin k → β) × 𝒲) (b : β), dist μ (pair (pair Yp Wv) Yl) (z, b) =
      dist μ (pair Yp Wv) z * W (enc k z.2 z.1) b := by
    rintro ⟨u, w⟩ b
    have hT : Function.Injective (pair (pair Yp Wv) Yl) := fun a c hac => by
      simp only [pair, Prod.mk.injEq, Yp, Yl, Wv] at hac
      refine Prod.ext hac.1.2 ?_
      rw [← Fin.snoc_init_self a.2, ← Fin.snoc_init_self c.2, hac.1.1, hac.2]
    have e1 : dist μ (pair (pair Yp Wv) Yl) ((u, w), b) = μ (w, Fin.snoc u b) := by
      have := dist_comp_of_injective μ id hT (w, Fin.snoc u b)
      rw [dist_id] at this
      simpa [pair, Yp, Yl, Wv, Fin.init_snoc] using this
    have e2 : dist μ (pair Yp Wv) (u, w) = fbLaw ν W enc k (w, u) := by
      have := dist_comp_of_injective μ (fun z => (z.1, Fin.init z.2)) Prod.swap_injective (w, u)
      rw [dist_fbLaw_init hW k] at this
      exact this
    rw [e1, e2]
    exact fbLaw_snoc k w u b
  have h5 := entropy_sub_condEntropy_eq_mutualInfoOf (fun z : (Fin k → β) × 𝒲 => enc k z.2 z.1)
    hμ hW hchan
  have h6 : mutualInfoOf (dist μ ((fun z : (Fin k → β) × 𝒲 => enc k z.2 z.1) ∘ pair Yp Wv)) W =
      mutualInfoOf (dist (fbLaw ν W enc (k + 1)) fun z => enc k z.1 (Fin.init z.2)) W := rfl
  rw [h1, h2, h3]
  linarith

/-- **(7.125)–(7.132)** Each channel use increases the mutual information between the message and
the outputs by at most the capacity: `I(W; Yᵏ⁺¹) ≤ I(W; Yᵏ) + C`. -/
theorem mutualInfo_fbLaw_succ_le (hν : IsPMF ν) (hW : IsChannel W) (k : ℕ) :
    I[Prod.fst : Prod.snd ; fbLaw ν W enc (k + 1)] ≤
      I[Prod.fst : Prod.snd ; fbLaw ν W enc k] + capacity W :=
  (mutualInfo_fbLaw_succ_le_mutualInfoOf hν hW k).trans
    (add_le_add_right (mutualInfoOf_le_capacity ((fbLaw_isPMF hν hW _).dist _) hW) _)

/-- **(7.125)–(7.132)** The message and the outputs of `n` uses of the channel, with or without
feedback, satisfy `I(W; Yⁿ) ≤ nC`. -/
theorem mutualInfo_fbLaw_le (hν : IsPMF ν) (hW : IsChannel W) (n : ℕ) :
    I[Prod.fst : Prod.snd ; fbLaw ν W enc n] ≤ n * capacity W := by
  induction n with
  | zero =>
    have hμ := fbLaw_isPMF (enc := enc) hν hW 0
    rw [mutualInfo_eq_entropy_sub_condEntropy' hμ]
    have h1 := entropyRV_le_log_card hμ (Prod.snd : 𝒲 × (Fin 0 → β) → Fin 0 → β)
    have h2 := condEntropy_nonneg hμ (Prod.snd : 𝒲 × (Fin 0 → β) → Fin 0 → β) Prod.fst
    simp only [Fintype.card_unique, Nat.cast_one, log_one] at h1
    simp only [CharP.cast_eq_zero, zero_mul]
    linarith
  | succ n ih =>
    have := mutualInfo_fbLaw_succ_le (enc := enc) hν hW n
    push_cast
    linarith

/-! ### Codes without feedback -/

/-- The encoder without feedback sending the codeword `x(w)`: the input at time `k + 1` is
`x(w)ₖ₊₁`, whatever the past outputs. -/
def nfEnc [Nonempty α] {n : ℕ} (x : 𝒲 → Fin n → α) : ∀ k, 𝒲 → (Fin k → β) → α :=
  fun k w _ => if h : k < n then x w ⟨k, h⟩ else Classical.arbitrary α

omit [Fintype α] [Fintype β] [Fintype 𝒲] in
/-- **(7.27)** Without feedback, the law of `(W, Yⁿ)` is `ν(w) p(yⁿ | xⁿ(w))`. -/
lemma fbLaw_nfEnc [Nonempty α] {n : ℕ} (x : 𝒲 → Fin n → α) (w : 𝒲) (y : Fin n → β) :
    fbLaw ν W (nfEnc x) n (w, y) = ν w * channelExt W n (x w) y := by
  have key : ∀ k (hk : k ≤ n) (u : Fin k → β),
      fbLaw ν W (nfEnc x) k (w, u) = ν w * ∏ i, W (x w (Fin.castLE hk i)) (u i) := by
    intro k
    induction k with
    | zero => intro _ u; simp [fbLaw]
    | succ k ih =>
      intro hk u
      have hkn : k < n := by omega
      rw [fbLaw, ih (by omega), Fin.prod_univ_castSucc]
      simp only [nfEnc, hkn, ↓reduceDIte, Fin.init]
      rw [mul_assoc]
      rfl
  rw [key n le_rfl y, channelExt]
  rfl

/-- **Lemma 7.9.2, (7.90)–(7.97).** For every input distribution `p(xⁿ)`, the input and the output
of `n` uses of a memoryless channel without feedback satisfy `I(Xⁿ; Yⁿ) ≤ nC`. -/
theorem mutualInfo_channelExt_le [Nonempty α] {n : ℕ} {P : (Fin n → α) → ℝ} (hP : IsPMF P)
    (hW : IsChannel W) :
    I[Prod.fst : Prod.snd ; fun z : (Fin n → α) × (Fin n → β) => P z.1 * channelExt W n z.1 z.2]
      ≤ n * capacity W := by
  have h : (fun z : (Fin n → α) × (Fin n → β) => P z.1 * channelExt W n z.1 z.2) =
      fbLaw P W (nfEnc id) n := funext fun z => (fbLaw_nfEnc id z.1 z.2).symm
  rw [h]
  exact mutualInfo_fbLaw_le hP hW n

/-! ### Fano's inequality and the converse -/

/-- **(7.98)–(7.102)** With feedback or without, a message with prior `ν`, decoded from the `n`
outputs with probability of error `Pₑ`, satisfies `H(W) ≤ log 2 + Pₑ log |𝒲| + nC`. -/
theorem entropy_le_of_fbLaw (hν : IsPMF ν) (hW : IsChannel W) {n : ℕ}
    (dec : (Fin n → β) → 𝒲) :
    H[Prod.fst ; fbLaw ν W enc n] ≤ log 2 +
      errProb (fbLaw ν W enc n) Prod.fst Prod.snd dec * log (Fintype.card 𝒲) + n * capacity W := by
  have hμ := fbLaw_isPMF (enc := enc) hν hW n
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ
    (Prod.fst : 𝒲 × (Fin n → β) → 𝒲) Prod.snd
  have h2 := fano_weak hμ (Prod.fst : 𝒲 × (Fin n → β) → 𝒲) Prod.snd dec
  have h3 := mutualInfo_fbLaw_le (enc := enc) hν hW n
  linarith

namespace ChannelCode

variable {M n : ℕ}

/-- The joint law `(1/M) p(yⁿ | xⁿ(w))` of a uniformly distributed message and the output. -/
def jointLaw [Nonempty α] (W : α → β → ℝ) (c : ChannelCode M n α β) :
    Fin M × (Fin n → β) → ℝ :=
  fbLaw (uniformPMF (Fin M)) W (nfEnc c.enc) n

omit [Fintype α] [Fintype β] in
lemma jointLaw_apply [Nonempty α] (c : ChannelCode M n α β) (w : Fin M) (y : Fin n → β) :
    c.jointLaw W (w, y) = 1 / M * channelExt W n (c.enc w) y := by
  rw [jointLaw, fbLaw_nfEnc]
  simp [uniformPMF]

omit [Fintype α] in
/-- **(7.32)** With a uniformly distributed message, `Pr{g(Yⁿ) ≠ W} = Pₑ^(n)`. -/
lemma errProb_jointLaw [Nonempty α] (c : ChannelCode M n α β) :
    errProb (c.jointLaw W) Prod.fst Prod.snd c.dec = c.avgErrProb W := by
  classical
  simp only [errProb, Fintype.sum_prod_type, jointLaw_apply, avgErrProb, condErrProb]
  rw [sum_div]
  refine sum_congr rfl fun w _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

omit [Fintype α] in
lemma entropy_fst_jointLaw [Nonempty α] (hW : IsChannel W) (hM : 0 < M)
    (c : ChannelCode M n α β) : H[Prod.fst ; c.jointLaw W] = log M := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hd : dist (c.jointLaw W) Prod.fst = uniformPMF (Fin M) := by
    funext w
    rw [dist_fst]
    simp only [jointLaw_apply, ← mul_sum, ((hW.ext n) (c.enc w)).sum_eq_one, mul_one,
      uniformPMF, Fintype.card_fin]
  rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_fin]

omit [Fintype α] in
/-- **Lemma 7.9.1 (Fano's inequality), (7.89).** For a code used with a uniformly distributed
message `W` and the estimate `Ŵ = g(Yⁿ)`, `H(W | Ŵ) ≤ log 2 + Pₑ^(n) log M`: in bits,
`H(W | Ŵ) ≤ 1 + Pₑ^(n) nR` for `M = 2^{nR}`. -/
theorem condEntropy_message_le [Nonempty α] (hW : IsChannel W) (c : ChannelCode M n α β) :
    H[Prod.fst | c.dec ∘ Prod.snd ; c.jointLaw W] ≤ log 2 + c.avgErrProb W * log M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have : IsEmpty (Fin 0 × (Fin n → β)) := inferInstance
    simp [condEntropy, dist, (log_pos one_lt_two).le]
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hμ : IsPMF (c.jointLaw W) := fbLaw_isPMF uniformPMF_isPMF hW n
  have h := fano_weak hμ (Prod.fst : Fin M × (Fin n → β) → Fin M) (c.dec ∘ Prod.snd) id
  have he : errProb (c.jointLaw W) Prod.fst (c.dec ∘ Prod.snd) id = c.avgErrProb W :=
    errProb_jointLaw c
  rwa [he, Fintype.card_fin] at h

/-- **(7.98)–(7.102)** Every `(M, n)` code satisfies `(1 - Pₑ^(n)) log M ≤ log 2 + nC`. -/
theorem one_sub_avgErrProb_mul_log_le [Nonempty α] (hW : IsChannel W) (hM : 0 < M)
    (c : ChannelCode M n α β) : (1 - c.avgErrProb W) * log M ≤ log 2 + n * capacity W := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have h := entropy_le_of_fbLaw (enc := nfEnc c.enc) (uniformPMF_isPMF (α := Fin M)) hW c.dec
  rw [← jointLaw, entropy_fst_jointLaw hW hM, errProb_jointLaw, Fintype.card_fin] at h
  linarith

/-- **(7.82)–(7.87)** A code with zero probability of error has `log M ≤ nC`: its rate is at most
the capacity. -/
theorem log_le_of_avgErrProb_eq_zero [Nonempty α] (hW : IsChannel W) (hM : 0 < M)
    (c : ChannelCode M n α β) (h0 : c.avgErrProb W = 0) : log M ≤ n * capacity W := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hμ : IsPMF (c.jointLaw W) := fbLaw_isPMF uniformPMF_isPMF hW n
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ
    (Prod.fst : Fin M × (Fin n → β) → Fin M) Prod.snd
  have h2 := condEntropy_eq_zero_of_errProb_eq_zero hμ (Prod.fst : Fin M × (Fin n → β) → Fin M)
    Prod.snd c.dec (by rw [errProb_jointLaw, h0])
  have h3 := mutualInfo_fbLaw_le (enc := nfEnc c.enc) (uniformPMF_isPMF (α := Fin M)) hW n
  rw [← jointLaw] at h3
  rw [entropy_fst_jointLaw hW hM] at h1
  linarith

/-- **(7.103)–(7.105)** A code of rate `R = (log M)/n > 0` has average probability of error
`Pₑ^(n) ≥ 1 - C/R - log 2/(nR)`: above capacity the error is bounded away from `0`. -/
theorem avgErrProb_ge [Nonempty α] (hW : IsChannel W) (hM : 0 < M) (hn : 0 < n)
    (c : ChannelCode M n α β) (hR : 0 < log M / n) :
    1 - capacity W / (log M / n) - log 2 / (n * (log M / n)) ≤ c.avgErrProb W := by
  have h := c.one_sub_avgErrProb_mul_log_le hW hM
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < log M := by
    have := mul_pos hR hn'
    rwa [div_mul_cancel₀ _ hn'.ne'] at this
  rw [mul_div_cancel₀ _ hn'.ne', div_div_eq_mul_div]
  have key : 1 - (log 2 + n * capacity W) / log M ≤ c.avgErrProb W := by
    rw [sub_le_comm, le_div_iff₀ hlog]
    linarith
  calc 1 - capacity W * n / log M - log 2 / log M
      = 1 - (log 2 + n * capacity W) / log M := by rw [add_div]; ring
    _ ≤ _ := key

end ChannelCode

/-- The limit argument of the converse, (7.103)–(7.104): if `(1 - Pₙ) log ⌈e^{nR}⌉ ≤ log 2 + nC`
for all `n ≥ 1` and `Pₙ → 0`, then `R ≤ C`. -/
lemma le_of_converse_bound {R C : ℝ} {P : ℕ → ℝ}
    (hP : Tendsto P atTop (𝓝 0)) (hP1 : ∀ n, P n ≤ 1)
    (h : ∀ n : ℕ, 0 < n → (1 - P n) * log ⌈exp (n * R)⌉₊ ≤ log 2 + n * C) : R ≤ C := by
  have hbound : ∀ᶠ n : ℕ in atTop, (1 - P n) * R ≤ log 2 / n + C := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : n * R ≤ log ⌈exp (n * R)⌉₊ :=
      calc n * R = log (exp (n * R)) := (log_exp _).symm
        _ ≤ log ⌈exp (n * R)⌉₊ := log_le_log (exp_pos _) (Nat.le_ceil _)
    have h5 : (1 - P n) * (n * R) ≤ log 2 + n * C :=
      (mul_le_mul_of_nonneg_left h2 (by linarith [hP1 n])).trans (h n hn)
    rw [div_add' _ _ _ hn'.ne', le_div_iff₀ hn']
    linarith
  have hlim : Tendsto (fun n : ℕ => log 2 / n + C) atTop (𝓝 C) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (log 2)).add_const C
  have hlim' : Tendsto (fun n => (1 - P n) * R) atTop (𝓝 R) := by
    simpa using (hP.const_sub 1).mul_const R
  exact le_of_tendsto_of_tendsto hlim' hlim hbound

/-- **Theorem 7.7.1 (converse), (7.98)–(7.104).** Any sequence of `(⌈e^{nR}⌉, n)` codes with
`λ^(n) → 0` must have `R ≤ C`. -/
theorem IsAchievableRate.le_capacity [Nonempty α] (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRate W R) : R ≤ capacity W := by
  obtain ⟨c, hc⟩ := h
  -- `Pₑ^(n) ≤ λ^(n) → 0`.
  have hPe : Tendsto (fun n => (c n).avgErrProb W) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun n => (c n).avgErrProb_nonneg hW) fun n => (c n).avgErrProb_le_maxErrProb
  refine le_of_converse_bound hPe (fun n => ?_) fun n _ =>
    (c n).one_sub_avgErrProb_mul_log_le hW (one_le_ceil_exp _)
  exact (c n).avgErrProb_le_maxErrProb.trans
    (ChannelCode.maxErrProb_le _ (one_le_ceil_exp _) fun i => (c n).condErrProb_le_one hW i)

/-- **Theorem 7.7.1 (Shannon's second theorem).** The operational capacity, the supremum of the
achievable rates, equals the information capacity `C = max_{p(x)} I(X; Y)`. -/
theorem opCapacity_eq_capacity [Nonempty α] (hW : IsChannel W) : opCapacity W = capacity W := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun R hR => hR.le_capacity hW) ?_
  · exact ⟨-1, isAchievableRate_of_lt_capacity hW (by linarith [capacity_nonneg hW])⟩
  · intro w hw
    exact ⟨(w + capacity W) / 2, isAchievableRate_of_lt_capacity hW (by linarith), by linarith⟩

/-! ### Feedback capacity -/

omit [Fintype α] in
/-- The message has law `ν` whatever the encoder. -/
lemma dist_fst_fbLaw (hW : IsChannel W) (k : ℕ) : dist (fbLaw ν W enc k) Prod.fst = ν := by
  induction k with
  | zero =>
    funext w
    rw [dist_fst]
    simp [fbLaw]
  | succ k ih =>
    calc dist (fbLaw ν W enc (k + 1)) Prod.fst
        = dist (dist (fbLaw ν W enc (k + 1)) fun z => (z.1, Fin.init z.2)) Prod.fst := by
          rw [← dist_comp_eq]; rfl
      _ = ν := by rw [dist_fbLaw_init hW k, ih]

/-- **Section 7.12.** A `(M, n)` feedback code: the input at time `k + 1` is
`enc k w (y₁, …, yₖ)`, a function of the message and of the past outputs, which are fed back
noiselessly to the transmitter. -/
structure FeedbackCode (M n : ℕ) (α β : Type*) where
  /-- The encoding functions `xₖ₊₁(w, y₁, …, yₖ)`. -/
  enc : ∀ k, Fin M → (Fin k → β) → α
  /-- The decoding function `g : 𝒴ⁿ → {0, …, M - 1}`. -/
  dec : (Fin n → β) → Fin M

/-- **(7.119)** The probability of error `Pₑ^(n) = Pr{g(Yⁿ) ≠ W}` of a feedback code, for a
uniformly distributed message. -/
def FeedbackCode.errProb {M n : ℕ} (W : α → β → ℝ) (c : FeedbackCode M n α β) : ℝ :=
  InfoTheory.errProb (fbLaw (uniformPMF (Fin M)) W c.enc n) Prod.fst Prod.snd c.dec

/-- **Definition (Section 7.12).** A rate `R` is achievable with feedback if there are
`(⌈e^{nR}⌉, n)` feedback codes with `Pₑ^(n) → 0`. -/
def IsAchievableRateFB (W : α → β → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, FeedbackCode ⌈exp (n * R)⌉₊ n α β,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Definition (Section 7.12).** The capacity with feedback `C_FB`, the supremum of the rates
achievable by feedback codes. -/
def fbCapacity (W : α → β → ℝ) : ℝ := sSup {R | IsAchievableRateFB W R}

/-- **(7.122)–(7.133)** Every `(M, n)` feedback code satisfies `(1 - Pₑ^(n)) log M ≤ log 2 + nC`. -/
theorem FeedbackCode.one_sub_errProb_mul_log_le {M n : ℕ} (hW : IsChannel W) (hM : 0 < M)
    (c : FeedbackCode M n α β) : (1 - c.errProb W) * log M ≤ log 2 + n * capacity W := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have h := entropy_le_of_fbLaw (enc := c.enc) (uniformPMF_isPMF (α := Fin M)) hW c.dec
  rw [entropyRV, dist_fst_fbLaw hW, entropy_uniformPMF, Fintype.card_fin] at h
  rw [FeedbackCode.errProb]
  linarith

omit [Fintype α] in
/-- A code without feedback is a feedback code, (7.121). -/
theorem IsAchievableRate.isAchievableRateFB [Nonempty α] (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRate W R) : IsAchievableRateFB W R := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun n => ⟨nfEnc (c n).enc, (c n).dec⟩, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun n => ?_)
    fun n => ?_
  · have : Nonempty (Fin ⌈exp (n * R)⌉₊) := ⟨⟨0, one_le_ceil_exp _⟩⟩
    exact errProb_nonneg (fbLaw_isPMF uniformPMF_isPMF hW n) _ _ _
  · change errProb ((c n).jointLaw W) _ _ _ ≤ _
    rw [ChannelCode.errProb_jointLaw]
    exact (c n).avgErrProb_le_maxErrProb

/-- **(7.122)–(7.134)** Rates achievable with feedback are at most the capacity. -/
theorem IsAchievableRateFB.le_capacity [Nonempty α] (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRateFB W R) : R ≤ capacity W := by
  obtain ⟨c, hc⟩ := h
  refine le_of_converse_bound hc (fun n => ?_) fun n _ =>
    (c n).one_sub_errProb_mul_log_le hW (one_le_ceil_exp _)
  have : Nonempty (Fin ⌈exp (n * R)⌉₊) := ⟨⟨0, one_le_ceil_exp _⟩⟩
  exact errProb_le_one (fbLaw_isPMF uniformPMF_isPMF hW n) _ _ _

/-- **Theorem 7.12.1 (Feedback capacity), (7.120).** Feedback does not increase the capacity of a
discrete memoryless channel: `C_FB = C = max_{p(x)} I(X; Y)`. -/
theorem fbCapacity_eq_capacity [Nonempty α] (hW : IsChannel W) : fbCapacity W = capacity W := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ (fun R hR => hR.le_capacity hW) ?_
  · exact ⟨-1, (isAchievableRate_of_lt_capacity hW
      (by linarith [capacity_nonneg hW])).isAchievableRateFB hW⟩
  · intro w hw
    exact ⟨(w + capacity W) / 2,
      (isAchievableRate_of_lt_capacity hW (by linarith)).isAchievableRateFB hW, by linarith⟩

end InfoTheory
