/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.AverageError
public import InfoTheoryLib.ChannelCoding.Cost

/-!
# Channels with state

A discrete memoryless channel with discrete memoryless state `(𝒳 × 𝒮, p(y | x, s) p(s), 𝒴)` is
given by a channel `W : α × σ → β → ℝ` and a pmf `p : σ → ℝ`. The state sequence is i.i.d. and is
known, or not, to the encoder and to the decoder. This file defines the codes, the achievable rates
and the capacity for each scenario, and treats the cases in which the channel with state reduces to
a channel without state.

## Main definitions

* `StateCode M n σ α β`: an encoder `xⁿ(m, sⁿ)` and a decoder `m̂(sⁿ, yⁿ)`.
* `EncoderStateInfo`, `StateCode.Allowed`: what the encoder knows (nothing, the state causally or
  noncausally) and whether the decoder knows the state, as restrictions on a `StateCode`.
* `IsAchievableStateRate`, `stateCapacity`: achievable rates in bits and the capacity.
* `strategyChannel W p e`: the channel `p(y | u) = ∑ₛ p(s) p(y | e(u, s), s)` obtained by attaching
  the device `x = e(u, s)` in front of the channel, and `strategyOutChannel W p e` the channel with
  output `(Y, S)`, `p(y, s | u) = p(s) p(y | e(u, s), s)`.
* `stateKnownValue W p`: the value `∑ₛ p(s) C_s`, where `C_s` is the capacity of `p(y | x, s)`.

## Main statements

* `stateCapacity_none_false`: without state information, the capacity is `max_{p(x)} I(X; Y)` with
  `p(y | x) = ∑ₛ p(s) p(y | x, s)`.
* `stateCapacity_none_true`: with the state at the decoder, it is `max_{p(x)} I(X; Y, S)`, and
  `mutualInfoOf_strategyOutChannel` gives `I(X; Y, S) = I(X; Y | S)`.
* `stateCapacity_causal_true`, `stateCapacity_noncausal_true`: with the state at the encoder,
  causally or noncausally, and at the decoder, it is `max_{p(x|s)} I(X; Y | S) = ∑ₛ p(s) C_s`.

## Implementation notes

All the scenarios use the same `StateCode`: a code that does not use some of the information has an
encoder or a decoder that does not depend on it. A decoder always outputs a message, as in
`ChannelCode`.

The notes prove achievability with the state at both ends by multiplexing the `|𝒮|` codebooks. We
use the Shannon strategy instead, the alternative that the notes mention on page 7-26: the
strategies `f : σ → α` with independent components `f(s) ∼ p*(x | s)` achieve `∑ₛ p(s) C_s`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 7
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {σ α β : Type*}

/-! ### Codes -/

/-- **Lecture 7 of [elgamal2010].** A code for the DMC with state: an encoder `xⁿ(m, sⁿ)` and a
decoder `m̂(sⁿ, yⁿ)`. -/
@[ext] structure StateCode (M n : ℕ) (σ α β : Type*) where
  /-- The encoder `xⁿ(m, sⁿ)`. -/
  enc : Fin M → (Fin n → σ) → Fin n → α
  /-- The decoder `m̂(sⁿ, yⁿ)`. -/
  dec : (Fin n → σ) → (Fin n → β) → Fin M

/-- What the encoder knows about the state sequence. -/
inductive EncoderStateInfo
  /-- The encoder does not know the state. -/
  | none
  /-- The encoder knows the state causally: `xᵢ(m, sⁱ)`. -/
  | causal
  /-- The encoder knows the whole state sequence in advance: `xⁿ(m, sⁿ)`. -/
  | noncausal

namespace StateCode

variable {M n : ℕ}

/-- The encoder does not use the state. -/
def EncIgnoresState (c : StateCode M n σ α β) : Prop := ∀ m s s', c.enc m s = c.enc m s'

/-- The encoder uses the state causally: `xᵢ` depends on `sⁿ` only through `s₁, …, sᵢ`. -/
def IsCausal (c : StateCode M n σ α β) : Prop :=
  ∀ m s s' i, (∀ j ≤ i, s j = s' j) → c.enc m s i = c.enc m s' i

/-- The decoder does not use the state. -/
def DecIgnoresState (c : StateCode M n σ α β) : Prop := ∀ s s' y, c.dec s y = c.dec s' y

/-- The code uses only the state information available in the scenario: `E` at the encoder, and at
the decoder if `D` holds. -/
def Allowed (E : EncoderStateInfo) (D : Bool) (c : StateCode M n σ α β) : Prop :=
  (match E with
    | .none => c.EncIgnoresState
    | .causal => c.IsCausal
    | .noncausal => True) ∧ (D = false → c.DecIgnoresState)

variable [Fintype σ] [Fintype β]

open Classical in
/-- The probability of error `P{M̂ ≠ M | M = m}`. -/
def condErr (W : α × σ → β → ℝ) (p : σ → ℝ) (c : StateCode M n σ α β) (m : Fin M) : ℝ :=
  ∑ s, iidPMF p n s * ∑ y,
    if c.dec s y ≠ m then channelExt W n (zipSeq (c.enc m s) s) y else 0

/-- The average probability of error `P_e^(n) = P{M̂ ≠ M}`. -/
def errProb (W : α × σ → β → ℝ) (p : σ → ℝ) (c : StateCode M n σ α β) : ℝ :=
  (∑ m, c.condErr W p m) / M

end StateCode

variable [Fintype σ] [Fintype β]

/-- **Lecture 7 of [elgamal2010].** A rate `R`, in bits, is achievable for the DMC with DM state in
the scenario `(E, D)` if there are `(2^{nR}, n)` codes using only the available state information,
whose average probability of error tends to `0`. -/
def IsAchievableStateRate (W : α × σ → β → ℝ) (p : σ → ℝ) (E : EncoderStateInfo) (D : Bool)
    (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, StateCode (2 ^ ⌈n * R⌉₊) n σ α β, (∀ n, (c n).Allowed E D) ∧
    Tendsto (fun n => (c n).errProb W p) atTop (𝓝 0)

/-- **Lecture 7 of [elgamal2010].** The capacity in the scenario `(E, D)`, in bits. -/
def stateCapacity (W : α × σ → β → ℝ) (p : σ → ℝ) (E : EncoderStateInfo) (D : Bool) : ℝ :=
  sSup {R | IsAchievableStateRate W p E D R}

/-! ### A converse helper -/

/-- If `(1 - Pₙ) log 2^⌈nR⌉ ≤ log 2 + n C` for all `n` and `Pₙ → 0`, then `R ≤ C / log 2`. -/
lemma le_div_log_two_of_converse {R C : ℝ} {P : ℕ → ℝ} (hP : Tendsto P atTop (𝓝 0))
    (hP1 : ∀ n, P n ≤ 1)
    (h : ∀ n : ℕ, (1 - P n) * log (2 ^ ⌈n * R⌉₊ : ℕ) ≤ log 2 + n * C) : R ≤ C / log 2 := by
  have key := le_of_converse_bound (R := R * log 2) (C := C) hP hP1 fun n _ => by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (by linarith [hP1 n])) (h n)
    exact log_le_log (Nat.cast_pos.2 (Nat.ceil_pos.2 (exp_pos _)))
      (by exact_mod_cast ceil_exp_le_two_pow n R)
  rwa [le_div_iff₀ (log_pos one_lt_two)]

/-! ### Input processing -/

section InputProcessing

variable {𝒰 𝒱 : Type*} [Fintype 𝒰] [Fintype 𝒱] {β' : Type*} [Fintype β']

/-- Processing the input by `g` before a channel does not change the information between what
enters the channel and the output: `I(U; Y) = I(g(U); Y)` for `U → g(U) → Y`. -/
lemma mutualInfoOf_comp {q : 𝒰 → ℝ} (hq : IsPMF q) {V : 𝒱 → β' → ℝ} (hV : IsChannel V)
    (g : 𝒰 → 𝒱) : mutualInfoOf q (V ∘ g) = mutualInfoOf (dist q g) V := by
  rw [mutualInfoOf_eq_sum (W := V ∘ g) hq (fun u => hV (g u)), mutualInfoOf_eq_sum (hq.dist g) hV,
    sum_dist_mul]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  rw [sum_dist_mul]
  rfl

/-- `I(U; Y) ≤ C` for `U → g(U) → Y`. -/
lemma mutualInfoOf_comp_le_capacity {q : 𝒰 → ℝ} (hq : IsPMF q) {V : 𝒱 → β' → ℝ}
    (hV : IsChannel V) (g : 𝒰 → 𝒱) : mutualInfoOf q (V ∘ g) ≤ capacity V := by
  rw [mutualInfoOf_comp hq hV]
  exact mutualInfoOf_le_capacity (hq.dist g) hV

end InputProcessing

/-! ### Strategies -/

section Strategy

variable {𝒰 : Type*}

/-- **Lecture 7 of [elgamal2010].** The channel `p(y | u) = ∑ₛ p(s) p(y | e(u, s), s)` obtained by
attaching the device `x = e(u, s)` in front of the channel. -/
def strategyChannel (W : α × σ → β → ℝ) (p : σ → ℝ) (e : 𝒰 → σ → α) : 𝒰 → β → ℝ :=
  fun u y => ∑ s, p s * W (e u s, s) y

/-- **Lecture 7 of [elgamal2010].** The same channel, with the state as a part of the output:
`p(y, s | u) = p(s) p(y | e(u, s), s)`. -/
def strategyOutChannel (W : α × σ → β → ℝ) (p : σ → ℝ) (e : 𝒰 → σ → α) : 𝒰 → β × σ → ℝ :=
  fun u z => p z.2 * W (e u z.2, z.2) z.1

lemma strategyChannel_isChannel {W : α × σ → β → ℝ} (hW : IsChannel W) {p : σ → ℝ} (hp : IsPMF p)
    (e : 𝒰 → σ → α) : IsChannel (strategyChannel W p e) := fun u => by
  refine ⟨fun y => sum_nonneg fun s _ => mul_nonneg (hp.nonneg s) ((hW _).nonneg y), ?_⟩
  simp only [strategyChannel]
  rw [sum_comm]
  simp only [← mul_sum, (hW _).sum_eq_one, mul_one, hp.sum_eq_one]

lemma strategyOutChannel_isChannel {W : α × σ → β → ℝ} (hW : IsChannel W) {p : σ → ℝ}
    (hp : IsPMF p) (e : 𝒰 → σ → α) : IsChannel (strategyOutChannel W p e) := fun u => by
  refine ⟨fun z => mul_nonneg (hp.nonneg _) ((hW _).nonneg _), ?_⟩
  simp only [strategyOutChannel]
  rw [Fintype.sum_prod_type_right]
  simp only [← mul_sum, (hW _).sum_eq_one, mul_one, hp.sum_eq_one]

omit [Fintype β] in
/-- The state sequence is i.i.d., so that the channel `p(y | u)` is memoryless. -/
lemma sum_iidPMF_mul_channelExt_zipSeq (W : α × σ → β → ℝ) (p : σ → ℝ) (e : 𝒰 → σ → α) {n : ℕ}
    (u : Fin n → 𝒰) (y : Fin n → β) :
    ∑ s, iidPMF p n s * channelExt W n (zipSeq (fun i => e (u i) (s i)) s) y =
      channelExt (strategyChannel W p e) n u y := by
  simp only [channelExt, zipSeq, strategyChannel]
  exact sum_iidPMF_mul_prod p fun i a => W (e (u i) a, a) (y i)

/-- The code for the DMC with state obtained from a code for `p(y | u)`: the encoder transmits
`xᵢ = e(uᵢ(m), sᵢ)` and the decoder does not use the state. -/
def ChannelCode.toStateCode {M n : ℕ} (c : ChannelCode M n 𝒰 β) (e : 𝒰 → σ → α) :
    StateCode M n σ α β :=
  ⟨fun m s i => e (c.enc m i) (s i), fun _ y => c.dec y⟩

/-- The code for the DMC with state obtained from a code for `p(y, s | u)`: the encoder transmits
`xᵢ = e(uᵢ(m), sᵢ)` and the decoder uses `(yⁿ, sⁿ)`. -/
def ChannelCode.toStateCodeOut {M n : ℕ} (c : ChannelCode M n 𝒰 (β × σ)) (e : 𝒰 → σ → α) :
    StateCode M n σ α β :=
  ⟨fun m s i => e (c.enc m i) (s i), fun s y => c.dec (zipSeq y s)⟩

/-- The code `c.toStateCode e` has the same probability of error over the channel with state as `c`
over `p(y | u)`. -/
theorem ChannelCode.errProb_toStateCode {M n : ℕ} (c : ChannelCode M n 𝒰 β) (e : 𝒰 → σ → α)
    (W : α × σ → β → ℝ) (p : σ → ℝ) :
    (c.toStateCode e).errProb W p = c.avgErrProb (strategyChannel W p e) := by
  classical
  simp only [StateCode.errProb, ChannelCode.avgErrProb]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  simp only [StateCode.condErr, ChannelCode.condErrProb, ChannelCode.toStateCode]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : c.dec y ≠ m
  · simp only [hy, ne_eq, not_false_eq_true, ite_true]
    exact sum_iidPMF_mul_channelExt_zipSeq W p e (c.enc m) y
  · simp [hy]

/-- The code `c.toStateCodeOut e` has the same probability of error over the channel with state as
`c` over `p(y, s | u)`. -/
theorem ChannelCode.errProb_toStateCodeOut {M n : ℕ} (c : ChannelCode M n 𝒰 (β × σ))
    (e : 𝒰 → σ → α) (W : α × σ → β → ℝ) (p : σ → ℝ) :
    (c.toStateCodeOut e).errProb W p = c.avgErrProb (strategyOutChannel W p e) := by
  classical
  simp only [StateCode.errProb, ChannelCode.avgErrProb]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  simp only [StateCode.condErr, ChannelCode.condErrProb, ChannelCode.toStateCodeOut]
  have hequiv := (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => β)
    (fun _ => σ)).symm.sum_comp fun z : Fin n → β × σ =>
    if c.dec z ≠ m then channelExt (strategyOutChannel W p e) n (c.enc m) z else 0
  rw [← hequiv, Fintype.sum_prod_type_right]
  refine sum_congr rfl fun s _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  have hz : (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => β) (fun _ => σ)).symm (y, s) =
      zipSeq y s := rfl
  rw [hz]
  by_cases hy : c.dec (zipSeq y s) ≠ m
  · simp only [hy, ne_eq, not_false_eq_true, ite_true]
    simp only [channelExt, zipSeq, strategyOutChannel, iidPMF, prod_mul_distrib]
  · simp [hy]

/-! ### The information with the state at the decoder -/

omit [Fintype σ] in
lemma sum_negMulLog_mul (a : ℝ) {r : β → ℝ} (hr : ∑ y, r y = 1) :
    ∑ y, negMulLog (a * r y) = negMulLog a + a * ∑ y, negMulLog (r y) := by
  simp_rw [Real.negMulLog_mul]
  rw [sum_add_distrib, ← sum_mul, hr, one_mul, mul_sum]

/-- **Lecture 7 of [elgamal2010], page 7-17.** With the state as a part of the output and `U`
independent of `S`, `I(U; Y, S) = I(U; Y | S) = ∑ₛ p(s) I(e(U, s); Y | S = s)`. -/
theorem mutualInfoOf_strategyOutChannel [Fintype α] [Fintype 𝒰] {W : α × σ → β → ℝ}
    (hW : IsChannel W) {p : σ → ℝ} (hp : IsPMF p) (e : 𝒰 → σ → α) {q : 𝒰 → ℝ} (hq : IsPMF q) :
    mutualInfoOf q (strategyOutChannel W p e) =
      ∑ s, p s * mutualInfoOf (dist q fun u => e u s) fun x => W (x, s) := by
  have hWs : ∀ s, IsChannel fun x => W (x, s) := fun s x => hW (x, s)
  rw [mutualInfoOf_eq_sum hq (strategyOutChannel_isChannel hW hp e)]
  simp_rw [entropy_eq_sum_negMulLog, Fintype.sum_prod_type_right, strategyOutChannel]
  have hout : ∀ s, ∑ y, ∑ u, q u * W (e u s, s) y = 1 := fun s => by
    rw [sum_comm]
    simp only [← mul_sum, (hW _).sum_eq_one, mul_one, hq.sum_eq_one]
  have h1 : ∀ s, ∑ y, negMulLog (∑ u, q u * (p s * W (e u s, s) y)) =
      negMulLog (p s) + p s * ∑ y, negMulLog (∑ u, q u * W (e u s, s) y) := fun s => by
    rw [← sum_negMulLog_mul (p s) (hout s)]
    refine sum_congr rfl fun y _ => ?_
    congr 1
    rw [mul_sum]
    exact sum_congr rfl fun u _ => by ring
  have h2 : ∀ u s, ∑ y, negMulLog (p s * W (e u s, s) y) =
      negMulLog (p s) + p s * ∑ y, negMulLog (W (e u s, s) y) := fun u s =>
    sum_negMulLog_mul (p s) (hW _).sum_eq_one
  have h3 : ∀ s, mutualInfoOf (dist q fun u => e u s) (fun x => W (x, s)) =
      ∑ y, negMulLog (∑ u, q u * W (e u s, s) y) -
        ∑ u, q u * ∑ y, negMulLog (W (e u s, s) y) := fun s => by
    rw [← mutualInfoOf_comp hq (hWs s), mutualInfoOf_eq_sum (W := (fun x => W (x, s)) ∘ _) hq
      (fun u => hWs s (e u s))]
    simp_rw [entropy_eq_sum_negMulLog]
    rfl
  simp_rw [h1, h2, h3, sum_add_distrib, mul_add, sum_add_distrib, ← sum_mul, hq.sum_eq_one, one_mul,
    mul_sub, sum_sub_distrib]
  rw [add_sub_add_left_eq_sub]
  congr 1
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

end Strategy

/-! ### Product strategies -/

section ProductPMF

variable {𝒜 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Fintype α]

/-- The pmf of a random function `f : 𝒜 → α` with independent values `f(a) ∼ P(a)`. -/
def prodPMF (P : 𝒜 → α → ℝ) : (𝒜 → α) → ℝ := fun f => ∏ a, P a (f a)

lemma prodPMF_isPMF {P : 𝒜 → α → ℝ} (hP : ∀ a, IsPMF (P a)) : IsPMF (prodPMF P) := by
  refine ⟨fun f => prod_nonneg fun a _ => (hP a).nonneg _, ?_⟩
  change ∑ f : 𝒜 → α, ∏ a, P a (f a) = 1
  rw [← Fintype.prod_sum]
  simp [(hP _).sum_eq_one]

/-- The value `f(a)` of the random function has the law `P(a)`. -/
lemma sum_prodPMF_mul_eval {P : 𝒜 → α → ℝ} (hP : ∀ a, IsPMF (P a)) (a : 𝒜) (g : α → ℝ) :
    ∑ f, prodPMF P f * g (f a) = ∑ x, P a x * g x := by
  have h : ∀ f : 𝒜 → α, prodPMF P f * g (f a) =
      ∏ b, (P b (f b) * if b = a then g (f b) else 1) := fun f => by
    rw [prod_mul_distrib, prod_ite_eq' univ a]
    simp [prodPMF]
  simp_rw [h]
  rw [← Fintype.prod_sum fun b y => P b y * if b = a then g y else 1, prod_eq_single a]
  · simp
  · intro b _ hb
    simp [hb, (hP b).sum_eq_one]
  · simp

/-- The value `f(a)` of the random function has the law `P(a)`. -/
lemma dist_prodPMF_eval {P : 𝒜 → α → ℝ} (hP : ∀ a, IsPMF (P a)) (a : 𝒜) :
    dist (prodPMF P) (fun f => f a) = P a := by
  classical
  funext x
  have := sum_prodPMF_mul_eval hP a fun y => if y = x then 1 else 0
  simpa [dist] using this

end ProductPMF

/-! ### Reductions to channels without state -/

section Reductions

variable {W : α × σ → β → ℝ} {p : σ → ℝ}

/-- Without state information, a code is a code for the channel `p(y | x) = ∑ₛ p(s) p(y | x, s)`. -/
theorem isAchievableStateRate_none_false_iff (hp : IsPMF p) {R : ℝ} :
    IsAchievableStateRate W p .none false R ↔
      IsAchievableRateAvg (strategyChannel W p fun x _ => x) R := by
  obtain ⟨s₀⟩ := hp.nonempty_type
  constructor
  · rintro ⟨c, hc, hlim⟩
    refine ⟨fun n => ⟨fun m => (c n).enc m fun _ => s₀, fun y => (c n).dec (fun _ => s₀) y⟩, ?_⟩
    refine hlim.congr fun n => ?_
    rw [← ChannelCode.errProb_toStateCode]
    congr 1
    refine StateCode.ext ?_ ?_
    · funext m s i
      exact congrFun ((hc n).1 m s _) i
    · funext s y
      exact (hc n).2 rfl s _ y
  · rintro ⟨c, hlim⟩
    refine ⟨fun n => (c n).toStateCode fun x _ => x, fun n => ⟨fun _ _ _ => rfl,
      fun _ _ _ _ => rfl⟩, hlim.congr fun n => ?_⟩
    rw [ChannelCode.errProb_toStateCode]

/-- With the state at the decoder only, a code is a code for the channel
`p(y, s | x) = p(s) p(y | x, s)`. -/
theorem isAchievableStateRate_none_true_iff (hp : IsPMF p) {R : ℝ} :
    IsAchievableStateRate W p .none true R ↔
      IsAchievableRateAvg (strategyOutChannel W p fun x _ => x) R := by
  obtain ⟨s₀⟩ := hp.nonempty_type
  constructor
  · rintro ⟨c, hc, hlim⟩
    refine ⟨fun n => ⟨fun m => (c n).enc m fun _ => s₀,
      fun z => (c n).dec (fun i => (z i).2) (fun i => (z i).1)⟩, ?_⟩
    refine hlim.congr fun n => ?_
    rw [← ChannelCode.errProb_toStateCodeOut]
    congr 1
    refine StateCode.ext ?_ rfl
    funext m s i
    exact congrFun ((hc n).1 m s _) i
  · rintro ⟨c, hlim⟩
    refine ⟨fun n => (c n).toStateCodeOut fun x _ => x, fun n => ⟨fun _ _ _ => rfl,
      by simp⟩, hlim.congr fun n => ?_⟩
    rw [ChannelCode.errProb_toStateCodeOut]

variable [Fintype α] [Nonempty α]

/-- **Lecture 7 of [elgamal2010], page 7-16.** With no state information, the capacity is
`C = max_{p(x)} I(X; Y)`, where `p(y | x) = ∑ₛ p(s) p(y | x, s)`, in bits. -/
theorem stateCapacity_none_false (hW : IsChannel W) (hp : IsPMF p) :
    stateCapacity W p .none false = capacity (strategyChannel W p fun x _ => x) / log 2 := by
  simp only [stateCapacity, isAchievableStateRate_none_false_iff hp]
  exact opCapacityAvg_eq (strategyChannel_isChannel hW hp _)

/-- **Lecture 7 of [elgamal2010], page 7-17.** With the state at the decoder only, the capacity is
`C_SI-D = max_{p(x)} I(X; Y, S)`, in bits. By `mutualInfoOf_strategyOutChannel`,
`I(X; Y, S) = I(X; Y | S)`. -/
theorem stateCapacity_none_true (hW : IsChannel W) (hp : IsPMF p) :
    stateCapacity W p .none true = capacity (strategyOutChannel W p fun x _ => x) / log 2 := by
  simp only [stateCapacity, isAchievableStateRate_none_true_iff hp]
  exact opCapacityAvg_eq (strategyOutChannel_isChannel hW hp _)

end Reductions

/-! ### The state at both the encoder and the decoder -/

section Both

variable [Fintype α] {W : α × σ → β → ℝ} {p : σ → ℝ}

/-- **Lecture 7 of [elgamal2010], page 7-17.** The value `max_{p(x|s)} I(X; Y | S) = ∑ₛ p(s) C_s`,
where `C_s` is the capacity of the channel `p(y | x, s)`. -/
def stateKnownValue (W : α × σ → β → ℝ) (p : σ → ℝ) : ℝ :=
  ∑ s, p s * capacity fun x => W (x, s)

omit [Fintype σ] [Fintype α] in
lemma channel_slice_isChannel (hW : IsChannel W) (s : σ) : IsChannel fun x => W (x, s) :=
  fun x => hW (x, s)

/-- `I(X; Y | S) ≤ ∑ₛ p(s) C_s` for every `p(x | s)`. -/
lemma sum_mul_mutualInfoOf_le_stateKnownValue (hW : IsChannel W) (hp : IsPMF p) {P : σ → α → ℝ}
    (hP : ∀ s, IsPMF (P s)) :
    ∑ s, p s * mutualInfoOf (P s) (fun x => W (x, s)) ≤ stateKnownValue W p :=
  sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (mutualInfoOf_le_capacity (hP s) (channel_slice_isChannel hW s)) (hp.nonneg s)

/-- `∑ₛ p(s) C_s` is attained by some `p(x | s)`. -/
lemma exists_sum_mul_mutualInfoOf_eq_stateKnownValue [Nonempty α] (hW : IsChannel W) :
    ∃ P : σ → α → ℝ, (∀ s, IsPMF (P s)) ∧
      ∑ s, p s * mutualInfoOf (P s) (fun x => W (x, s)) = stateKnownValue W p := by
  choose P hP hPC using fun s => exists_capacity_eq (channel_slice_isChannel hW s)
  exact ⟨P, hP, sum_congr rfl fun s _ => by rw [hPC]⟩

/-- The strategies `f : σ → α` with `f(s) ∼ p*(x | s)` independent achieve `∑ₛ p(s) C_s`. -/
theorem capacity_strategyOutChannel_id [DecidableEq σ] [Nonempty α] (hW : IsChannel W)
    (hp : IsPMF p) :
    capacity (strategyOutChannel W p fun f : σ → α => f) = stateKnownValue W p := by
  refine le_antisymm ?_ ?_
  · obtain ⟨q, hq, hqC⟩ := exists_capacity_eq (strategyOutChannel_isChannel hW hp
      fun f : σ → α => f)
    rw [← hqC, mutualInfoOf_strategyOutChannel hW hp _ hq]
    exact sum_mul_mutualInfoOf_le_stateKnownValue hW hp fun s => hq.dist _
  · obtain ⟨P, hP, hPC⟩ := exists_sum_mul_mutualInfoOf_eq_stateKnownValue (p := p) hW
    have hq := prodPMF_isPMF hP
    have h := mutualInfoOf_le_capacity hq (strategyOutChannel_isChannel hW hp fun f : σ → α => f)
    rw [mutualInfoOf_strategyOutChannel hW hp _ hq] at h
    simp_rw [dist_prodPMF_eval hP] at h
    rwa [hPC] at h

/-- The code for `n` uses of the channel `p(y | x, s)` when the state sequence is `sⁿ`. -/
def StateCode.atState {M n : ℕ} (c : StateCode M n σ α β) (s : Fin n → σ) :
    ChannelCode M n (α × σ) β :=
  ⟨fun m => zipSeq (c.enc m s) s, c.dec s⟩

omit [Fintype α] in
/-- `P_e^(n) = E P{M̂ ≠ M | Sⁿ}`. -/
lemma StateCode.errProb_eq_sum_atState {M n : ℕ} (c : StateCode M n σ α β) :
    c.errProb W p = ∑ s, iidPMF p n s * (c.atState s).avgErrProb W := by
  simp only [StateCode.errProb, ChannelCode.avgErrProb, StateCode.condErr]
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun s _ => ?_
  rw [← mul_sum, mul_div_assoc]
  rfl

omit [Fintype α] in
lemma StateCode.errProb_le_one (hW : IsChannel W) (hp : IsPMF p) {M n : ℕ} (hM : 0 < M)
    (c : StateCode M n σ α β) : c.errProb W p ≤ 1 := by
  have hi := iidPMF_isPMF hp n
  rw [c.errProb_eq_sum_atState, ← hi.sum_eq_one]
  refine sum_le_sum fun s _ => mul_le_of_le_one_right (hi.nonneg s) ?_
  exact (c.atState s).avgErrProb_le_maxErrProb.trans
    (ChannelCode.maxErrProb_le _ hM fun i => (c.atState s).condErrProb_le_one hW i)

/-- Conditioned on `Sⁿ = sⁿ`, the code is a code for `n` uses of the channel with the known states
`s₁, …, sₙ`, so that `(1 - P_e^(n)) log M ≤ log 2 + ∑ᵢ E C_{Sᵢ} = log 2 + n ∑ₛ p(s) C_s`. This
is the converse of the capacity with the state at both ends, also for the noncausal encoder. -/
theorem StateCode.one_sub_errProb_mul_log_le [Nonempty α] (hW : IsChannel W) (hp : IsPMF p)
    {M n : ℕ} (hM : 0 < M) (c : StateCode M n σ α β) :
    (1 - c.errProb W p) * log M ≤ log 2 + n * stateKnownValue W p := by
  have : Nonempty σ := hp.nonempty_type
  set C : σ → ℝ := fun s => capacity fun x => W (x, s)
  have hbound : ∀ s, (1 - (c.atState s).avgErrProb W) * log M ≤ log 2 + ∑ i, C (s i) := by
    intro s
    refine ((c.atState s).one_sub_avgErrProb_mul_log_le_sum hW hM).trans
      (add_le_add le_rfl (sum_le_sum fun i _ => ?_))
    have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    have hν : IsPMF (uniformPMF (Fin M)) := uniformPMF_isPMF
    rw [← mutualInfoOf_comp hν hW]
    exact mutualInfoOf_comp_le_capacity hν (channel_slice_isChannel hW (s i)) _
  have hi := iidPMF_isPMF hp n
  have hsum := sum_le_sum fun s (_ : s ∈ univ) =>
    mul_le_mul_of_nonneg_left (hbound s) (hi.nonneg s)
  have hl : ∑ s, iidPMF p n s * ((1 - (c.atState s).avgErrProb W) * log M) =
      (1 - c.errProb W p) * log M := by
    have h : ∀ s, iidPMF p n s * ((1 - (c.atState s).avgErrProb W) * log M) =
        (iidPMF p n s - iidPMF p n s * (c.atState s).avgErrProb W) * log M := fun s => by ring
    simp_rw [h]
    rw [← sum_mul, sum_sub_distrib, hi.sum_eq_one, c.errProb_eq_sum_atState]
  have hr : ∑ s, iidPMF p n s * (log 2 + ∑ i, C (s i)) = log 2 + n * stateKnownValue W p := by
    simp_rw [mul_add, mul_sum]
    rw [sum_add_distrib, ← sum_mul, hi.sum_eq_one, one_mul, sum_comm]
    congr 1
    have : ∀ i : Fin n, ∑ s, iidPMF p n s * C (s i) = stateKnownValue W p := fun i =>
      sum_iidPMF_eval hp i C
    simp [this]
  rw [hl, hr] at hsum
  exact hsum

/-- The converse: a rate that is achievable in any scenario is at most `∑ₛ p(s) C_s`, in bits. -/
theorem IsAchievableStateRate.le_stateKnownValue [Nonempty α] (hW : IsChannel W) (hp : IsPMF p)
    {E : EncoderStateInfo} {D : Bool} {R : ℝ} (h : IsAchievableStateRate W p E D R) :
    R ≤ stateKnownValue W p / log 2 := by
  obtain ⟨c, -, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈n * R⌉₊ := fun n => by positivity
  exact le_div_log_two_of_converse hc (fun n => (c n).errProb_le_one hW hp (hpos n))
    fun n => (c n).one_sub_errProb_mul_log_le hW hp (hpos n)

omit [Fintype α] in
/-- A code using the state causally at the encoder is a code using it noncausally. -/
lemma IsAchievableStateRate.causal_noncausal {D : Bool} {R : ℝ}
    (h : IsAchievableStateRate W p .causal D R) : IsAchievableStateRate W p .noncausal D R := by
  obtain ⟨c, hc, hlim⟩ := h
  exact ⟨c, fun n => ⟨trivial, (hc n).2⟩, hlim⟩

/-- Achievability with the state known at both ends, by the Shannon strategy. -/
theorem isAchievableStateRate_causal_true_of_lt [Nonempty α] (hW : IsChannel W) (hp : IsPMF p)
    {R : ℝ} (hR : R < stateKnownValue W p / log 2) : IsAchievableStateRate W p .causal true R := by
  classical
  rw [← capacity_strategyOutChannel_id hW hp] at hR
  obtain ⟨c, hlim⟩ := isAchievableRateAvg_of_lt (strategyOutChannel_isChannel hW hp _) hR
  refine ⟨fun n => (c n).toStateCodeOut fun f => f, fun n => ⟨?_, by simp⟩, hlim.congr fun n => ?_⟩
  · intro m s s' i h
    change ((c n).enc m i) (s i) = ((c n).enc m i) (s' i)
    rw [h i le_rfl]
  · rw [ChannelCode.errProb_toStateCodeOut]

/-- **Lecture 7 of [elgamal2010], page 7-17.** With the state available causally at both the encoder
and the decoder, the capacity is `C_SI-ED = max_{p(x|s)} I(X; Y | S)`, in bits. -/
theorem stateCapacity_causal_true [Nonempty α] (hW : IsChannel W) (hp : IsPMF p) :
    stateCapacity W p .causal true = stateKnownValue W p / log 2 :=
  sSup_eq_of_forall_mem (fun _ h => h.le_stateKnownValue hW hp)
    fun _ hR => isAchievableStateRate_causal_true_of_lt hW hp hR

/-- **Lecture 7 of [elgamal2010], page 7-17.** With the state available noncausally at both the
encoder and the decoder, the capacity is also `C_SI-ED = max_{p(x|s)} I(X; Y | S)`, in bits. -/
theorem stateCapacity_noncausal_true [Nonempty α] (hW : IsChannel W) (hp : IsPMF p) :
    stateCapacity W p .noncausal true = stateKnownValue W p / log 2 :=
  sSup_eq_of_forall_mem (fun _ h => h.le_stateKnownValue hW hp)
    fun _ hR => (isAchievableStateRate_causal_true_of_lt hW hp hR).causal_noncausal

end Both

end InfoTheory
