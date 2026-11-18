/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.Network.BCDegradedLaws
public import InfoTheoryLib.Network.Broadcast

/-!
# The discrete memoryless relay channel: codes and the cutset bound

The problem setup of Lecture 17 of El Gamal and Kim, and Theorem 1. The channel is `W : X × X₁ →
Y × Y₁ → ℝ`. At time `k` the relay sends a function of the first `k` symbols it has received.

## Main definitions

* `RCCode M n X X₁ Y Y₁`: `(M, n)` codes for the relay channel.
* `RCCode.law`, `RCCode.errProb`: the joint law, and the probability of error.
* `IsAchievableRC`, `rcCapacity`: achievable rates, in bits, and the capacity.
* `rcMacInfo p W`, `rcBcInfo p W`: `I(X, X₁; Y)` and `I(X; Y, Y₁ | X₁)`, in nats.
* `rcCutsetBound W`: `max_{p(x, x₁)} min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)}`.

## Main statements

* `RCCode.one_sub_errProb_mul_log_le`: the bound for each code.
* `IsAchievableRC.le_rcCutsetBound`: **Theorem 1 of Lecture 17, the cutset bound.**

## Implementation notes

The law of the code is `fbLaw` of the channel coding converse: for the channel from `(X, X₁)` to
`(Y, Y₁)`, the pair of an encoder and a relay is an encoder with feedback of `(Y, Y₁)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### General facts on laws -/

section General

variable {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]

omit [Fintype a] [Fintype b] in
/-- The law of `(T, U₁)` is a marginal of the law of `(T, (U₁, U₂))`. -/
lemma dist_pair_marg_fst {b₂ : Type*} [Fintype b₂] (μ : Ω → ℝ) (T : Ω → a) (U : Ω → b × b₂)
    (t : a) (y : b) :
    dist μ (pair T fun ω => (U ω).1) (t, y) = ∑ y₂, dist μ (pair T U) (t, (y, y₂)) := by
  classical
  simp only [dist]
  rw [sum_comm]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : T ω = t ∧ (U ω).1 = y
  · have hU : U ω = (y, (U ω).2) := Prod.ext h.2 rfl
    rw [Finset.sum_eq_single (U ω).2]
    · rw [ite_eq_left (show pair T (fun ω => (U ω).1) ω = (t, y) by simp [pair, h.1, h.2]),
        ite_eq_left (show pair T U ω = (t, y, (U ω).2) by
          simp only [pair, h.1]
          exact congrArg _ hU)]
    · intro y₂ _ hy₂
      refine ite_eq_right fun he => hy₂ ?_
      have := congrArg (fun z => z.2.2) he
      simpa [pair] using this.symm
    · simp
  · rw [ite_eq_right (show ¬ pair T (fun ω => (U ω).1) ω = (t, y) by
      simpa [pair, Prod.ext_iff] using h)]
    refine (Finset.sum_eq_zero fun y₂ _ => ite_eq_right fun he => h ?_).symm
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg (fun z => z.2.1) he
    exact ⟨by simpa [pair] using h₁, by simpa [pair] using h₂⟩

end General

/-! ### Feedback laws -/

section Feedback

variable {𝒲 α β : Type*} [Fintype 𝒲] [Fintype β] {ν : 𝒲 → ℝ} {W : α → β → ℝ}
  {enc : ∀ k, 𝒲 → (Fin k → β) → α}

/-- Given `(Yᵏ, W) = (u, w)`, `Yₖ₊₁` is the output of the channel for the input `enc k w u`. -/
lemma dist_fbLaw_chan (hW : IsChannel W) (k : ℕ) (z : (Fin k → β) × 𝒲) (b : β) :
    dist (fbLaw ν W enc (k + 1)) (pair (pair (fun z => Fin.init z.2) Prod.fst)
        fun z => z.2 (Fin.last k)) (z, b) =
      dist (fbLaw ν W enc (k + 1)) (pair (fun z => Fin.init z.2) Prod.fst) z *
        W (enc k z.2 z.1) b := by
  classical
  obtain ⟨u, w⟩ := z
  set μ := fbLaw ν W enc (k + 1)
  have hT : Function.Injective (pair (pair (fun z : 𝒲 × (Fin (k + 1) → β) => Fin.init z.2)
      Prod.fst) fun z => z.2 (Fin.last k)) := fun a c hac => by
    simp only [pair, Prod.mk.injEq] at hac
    refine Prod.ext hac.1.2 ?_
    rw [← Fin.snoc_init_self a.2, ← Fin.snoc_init_self c.2, hac.1.1, hac.2]
  have e1 : dist μ (pair (pair (fun z => Fin.init z.2) Prod.fst) fun z => z.2 (Fin.last k))
      ((u, w), b) = μ (w, Fin.snoc u b) := by
    have := dist_comp_of_injective μ id hT (w, Fin.snoc u b)
    rw [dist_id] at this
    simpa [pair, Fin.init_snoc] using this
  have e2 : dist μ (pair (fun z => Fin.init z.2) Prod.fst) (u, w) = fbLaw ν W enc k (w, u) := by
    have := dist_comp_of_injective μ (fun z => (z.1, Fin.init z.2)) Prod.swap_injective (w, u)
    rw [dist_fbLaw_init hW k] at this
    exact this
  rw [e1, e2]
  exact fbLaw_snoc k w u b

end Feedback

section FB

variable {𝒲 α β : Type*} {ν : 𝒲 → ℝ} {W : α → β → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β) → α}

/-- **The closed form of a feedback law.** -/
lemma fbLaw_eq_prod (k : ℕ) (w : 𝒲) (z : Fin k → β) :
    fbLaw ν W enc k (w, z) =
      ν w * ∏ i : Fin k, W (enc i w fun t : Fin i => z ⟨t, t.2.trans i.2⟩) (z i) := by
  induction k with
  | zero => simp [fbLaw]
  | succ k ih =>
    rw [fbLaw, Fin.prod_univ_castSucc, ih, mul_assoc]
    rfl

end FB

/-! ### Codes -/

variable {X X₁ Y Y₁ : Type*}

/-- **Lecture 17 of [elgamal2010], page 17-2.** An `(M, n)` code for the relay channel: the sender
sends `enc k m` at time `k`, the relay sends `relay k (y₁₀, …, y₁,ₖ₋₁)`, and the receiver decodes
from `yⁿ`. Times are numbered from `0`. -/
structure RCCode (M n : ℕ) (X X₁ Y Y₁ : Type*) where
  /-- The encoder. -/
  enc : ℕ → Fin M → X
  /-- The relay encoder. -/
  relay : ∀ k, (Fin k → Y₁) → X₁
  /-- The decoder. -/
  dec : (Fin n → Y) → Fin M

section Law

variable [Fintype Y] [Fintype Y₁] {M n : ℕ}

/-- The pair of the encoder and the relay, as an encoder with feedback. -/
def RCCode.fbEnc (c : RCCode M n X X₁ Y Y₁) : ∀ k, Fin M → (Fin k → Y × Y₁) → X × X₁ :=
  fun k m z => (c.enc k m, c.relay k fun i => (z i).2)

/-- The joint law of the message and of the first `k` outputs, for a uniform message. -/
def RCCode.law (c : RCCode M n X X₁ Y Y₁) (W : X × X₁ → Y × Y₁ → ℝ) (k : ℕ) :
    Fin M × (Fin k → Y × Y₁) → ℝ :=
  fbLaw (uniformPMF (Fin M)) W c.fbEnc k

/-- **Page 17-3 of [elgamal2010].** The average probability of error. -/
def RCCode.errProb (c : RCCode M n X X₁ Y Y₁) (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  InfoTheory.errProb (c.law W n) Prod.fst (fun z i => (z.2 i).1) c.dec

/-- **Page 17-3 of [elgamal2010].** A rate, in bits, is achievable if there are codes with
`2 ^ ⌈n R⌉` messages whose probability of error tends to zero. -/
def IsAchievableRC (W : X × X₁ → Y × Y₁ → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, RCCode (2 ^ ⌈(n : ℝ) * R⌉₊) n X X₁ Y Y₁,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Page 17-3 of [elgamal2010].** The capacity, in bits. -/
def rcCapacity (W : X × X₁ → Y × Y₁ → ℝ) : ℝ := sSup {R | IsAchievableRC W R}

/-- **Page 18-43 of [elgamal2010].** An `(M, n)` code for the relay channel with feedback from both
receivers: the sender and the relay see all the past outputs. -/
structure RCFBCode (M n : ℕ) (X X₁ Y Y₁ : Type*) where
  /-- The encoder. -/
  enc : ∀ k, Fin M → (Fin k → Y × Y₁) → X
  /-- The relay encoder. -/
  relay : ∀ k, (Fin k → Y × Y₁) → X₁
  /-- The decoder. -/
  dec : (Fin n → Y) → Fin M

/-- The pair of the encoder and the relay, as an encoder with feedback. -/
def RCFBCode.fbEnc (c : RCFBCode M n X X₁ Y Y₁) : ∀ k, Fin M → (Fin k → Y × Y₁) → X × X₁ :=
  fun k m z => (c.enc k m z, c.relay k z)

/-- The joint law of the message and of the first `k` outputs, for a uniform message. -/
def RCFBCode.law (c : RCFBCode M n X X₁ Y Y₁) (W : X × X₁ → Y × Y₁ → ℝ) (k : ℕ) :
    Fin M × (Fin k → Y × Y₁) → ℝ :=
  fbLaw (uniformPMF (Fin M)) W c.fbEnc k

/-- The average probability of error. -/
def RCFBCode.errProb (c : RCFBCode M n X X₁ Y Y₁) (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  InfoTheory.errProb (c.law W n) Prod.fst (fun z i => (z.2 i).1) c.dec

/-- A code without feedback is a code with feedback that ignores it. -/
def RCCode.toFB (c : RCCode M n X X₁ Y Y₁) : RCFBCode M n X X₁ Y Y₁ where
  enc k m _ := c.enc k m
  relay k z := c.relay k fun i => (z i).2
  dec := c.dec

/-- **Page 18-43 of [elgamal2010].** A rate is achievable with feedback. -/
def IsAchievableRCFB (W : X × X₁ → Y × Y₁ → ℝ) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, RCFBCode (2 ^ ⌈(n : ℝ) * R⌉₊) n X X₁ Y Y₁,
    Tendsto (fun n => (c n).errProb W) atTop (𝓝 0)

/-- **Page 18-43 of [elgamal2010].** The capacity with feedback, in bits. -/
def rcfbCapacity (W : X × X₁ → Y × Y₁ → ℝ) : ℝ := sSup {R | IsAchievableRCFB W R}

end Law

/-! ### Conditional information for a channel -/

section CInfo

variable {A B Z : Type*} [Fintype A] [Fintype B] [Fintype Z]

/-- `I(A; Z | B)`, in nats, for an input law `p(a, b)` and a channel `p(z | a, b)`. -/
def cInfo (p : A × B → ℝ) (T : A × B → Z → ℝ) : ℝ :=
  I[fun z : (A × B) × Z => z.1.1 : Prod.snd | fun z => z.1.2 ; jointOf p T]

variable {p : A × B → ℝ} {T : A × B → Z → ℝ}

/-- `I(A; Z | B) = H(Z | B) - H(Z | A, B)`. -/
lemma cInfo_eq (hp : IsPMF p) (hT : IsChannel T) :
    cInfo p T = H[Prod.snd | fun z : (A × B) × Z => z.1.2 ; jointOf p T] -
      ∑ a, p a * entropy (T a) := by
  have hμ := jointOf_isPMF hp hT
  rw [cInfo, condMutualInfo_comm hμ, condMutualInfo_eq' hμ, ← condEntropy_jointOf hp hT]
  congr 1
  refine condEntropy_congr_right hμ Prod.snd (X := (Prod.fst : (A × B) × Z → A × B))
    (fun t => (t.2, t.1)) (fun a b hab => ?_) fun z => rfl
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext hab.2 hab.1

/-- `I(A; Z | B)` is concave in `p(a, b)`. -/
lemma sum_cInfo_le {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : IsPMF w) {q : ι → A × B → ℝ}
    (hq : ∀ i, IsPMF (q i)) (hT : IsChannel T) :
    ∑ i, w i * cInfo (q i) T ≤ cInfo (fun a => ∑ i, w i * q i a) T := by
  classical
  have hp : IsPMF fun a => ∑ i, w i * q i a := by
    refine ⟨fun a => sum_nonneg fun i _ => mul_nonneg (hw.nonneg i) ((hq i).nonneg a), ?_⟩
    rw [sum_comm]
    simp_rw [← mul_sum, (hq _).sum_eq_one, mul_one, hw.sum_eq_one]
  simp_rw [cInfo_eq (hq _) hT]
  rw [cInfo_eq hp hT]
  simp_rw [mul_sub, sum_sub_distrib]
  have hlin : ∑ a, (∑ i, w i * q i a) * entropy (T a) =
      ∑ i, w i * ∑ a, q i a * entropy (T a) := by
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun a _ => mul_assoc _ _ _
  rw [hlin]
  -- the mixture over `ι`
  let ν : ι × ((A × B) × Z) → ℝ := fun z => w z.1 * jointOf (q z.1) T z.2
  have hν : IsPMF ν := by
    refine ⟨fun z => mul_nonneg (hw.nonneg _) ((jointOf_isPMF (hq _) hT).nonneg _), ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [ν]
    simp_rw [← mul_sum, (jointOf_isPMF (hq _) hT).sum_eq_one, mul_one, hw.sum_eq_one]
  have hmix := condEntropy_mixture w (fun i => jointOf (q i) T)
    (fun _ => (Prod.snd : (A × B) × Z → Z)) (fun _ z => z.1.2)
  have hle := condEntropy_le_condEntropy_comp hν (fun z => z.2.2)
    (fun z : ι × ((A × B) × Z) => (z.1, z.2.1.2)) Prod.snd
  have hmarg : H[fun z : ι × ((A × B) × Z) => z.2.2 | Prod.snd ∘ fun z => (z.1, z.2.1.2) ;
      ν] = H[Prod.snd | fun z : (A × B) × Z => z.1.2 ;
        jointOf (fun a => ∑ i, w i * q i a) T] := by
    refine condEntropy_eq_of_dist_pair_eq hν (jointOf_isPMF hp hT) ?_
    have hd : dist ν Prod.snd = jointOf (fun a => ∑ i, w i * q i a) T := by
      funext t
      simp only [dist]
      rw [Fintype.sum_prod_type]
      simp only [ν, jointOf]
      rw [sum_mul]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single t]
      · simp [mul_assoc]
      · intro y _ h
        simp [h]
      · simp
    have h₁ : pair (Prod.snd ∘ fun z : ι × ((A × B) × Z) => (z.1, z.2.1.2))
        (fun z => z.2.2) = (pair (fun z : (A × B) × Z => z.1.2) Prod.snd) ∘ Prod.snd := rfl
    rw [h₁, dist_comp_eq, hd]
  have : ∑ i, w i * H[Prod.snd | fun z : (A × B) × Z => z.1.2 ; jointOf (q i) T] ≤
      H[Prod.snd | fun z : (A × B) × Z => z.1.2 ;
        jointOf (fun a => ∑ i, w i * q i a) T] := by
    rw [← hmix, ← hmarg]
    exact hle
  linarith

end CInfo

/-! ### The informations of the cutset bound -/

section Info

variable [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]

/-- `I(X, X₁; Y)`, in nats, for the input law `p(x, x₁)`. -/
def rcMacInfo (p : X × X₁ → ℝ) (W : X × X₁ → Y × Y₁ → ℝ) : ℝ := mutualInfoOf p (bcMarg₁ W)

/-- `I(X; Y, Y₁ | X₁)`, in nats, for the input law `p(x, x₁)`. -/
def rcBcInfo (p : X × X₁ → ℝ) (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : Prod.snd | fun z => z.1.2 ; jointOf p W]

variable {p : X × X₁ → ℝ} {W : X × X₁ → Y × Y₁ → ℝ}

/-- `I(X; Y, Y₁ | X₁) = H(Y, Y₁ | X₁) - H(Y, Y₁ | X, X₁)`. -/
lemma rcBcInfo_eq (hp : IsPMF p) (hW : IsChannel W) :
    rcBcInfo p W = H[Prod.snd | fun z : (X × X₁) × (Y × Y₁) => z.1.2 ; jointOf p W] -
      ∑ a, p a * entropy (W a) := by
  have hμ := jointOf_isPMF hp hW
  rw [rcBcInfo, condMutualInfo_comm hμ, condMutualInfo_eq' hμ, ← condEntropy_jointOf hp hW]
  congr 1
  refine condEntropy_congr_right hμ Prod.snd (X := (Prod.fst : (X × X₁) × (Y × Y₁) → X × X₁))
    (fun t => (t.2, t.1)) (fun a b hab => ?_) fun z => rfl
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext hab.2 hab.1

/-- `I(X; Y, Y₁ | X₁)` is concave in `p(x, x₁)`. -/
lemma sum_rcBcInfo_le {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : IsPMF w) {q : ι → X × X₁ → ℝ}
    (hq : ∀ i, IsPMF (q i)) (hW : IsChannel W) :
    ∑ i, w i * rcBcInfo (q i) W ≤ rcBcInfo (fun a => ∑ i, w i * q i a) W :=
  sum_cInfo_le hw hq hW

end Info

/-! ### One use of the channel -/

section Step

variable [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁] {M n : ℕ}
  {W : X × X₁ → Y × Y₁ → ℝ}

/-- The law of the inputs at time `k`. -/
def RCFBCode.letter (c : RCFBCode M n X X₁ Y Y₁) (W : X × X₁ → Y × Y₁ → ℝ) (k : ℕ) : X × X₁ → ℝ :=
  dist (c.law W (k + 1)) fun z => c.fbEnc k z.1 (Fin.init z.2)

omit [Fintype X] [Fintype X₁] in
lemma RCFBCode.law_isPMF (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M) (hW : IsChannel W) (k : ℕ) :
    IsPMF (c.law W k) := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  exact fbLaw_isPMF uniformPMF_isPMF hW k

lemma RCFBCode.letter_isPMF (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M) (hW : IsChannel W) (k : ℕ) :
    IsPMF (c.letter W k) :=
  (c.law_isPMF hM hW (k + 1)).dist _

/-- The received symbols. -/
def rcY {M k : ℕ} : Fin M × (Fin k → Y × Y₁) → Fin k → Y := fun z i => (z.2 i).1

/-- `I(M; Yᵏ⁺¹) ≤ I(M; Yᵏ) + I(Xₖ, X₁ₖ; Yₖ)`, page 17-6 of [elgamal2010]. -/
theorem RCFBCode.mutualInfo_succ_le_mac (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M) (hW : IsChannel W)
    (k : ℕ) :
    I[Prod.fst : rcY ; c.law W (k + 1)] ≤
      I[Prod.fst : rcY ; c.law W k] + rcMacInfo (c.letter W k) W := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set μ := c.law W (k + 1) with hμdef
  have hμ : IsPMF μ := c.law_isPMF hM hW (k + 1)
  let Zp : Fin M × (Fin (k + 1) → Y × Y₁) → (Fin k → Y × Y₁) := fun z => Fin.init z.2
  let Yp : Fin M × (Fin (k + 1) → Y × Y₁) → (Fin k → Y) := fun z i => (Zp z i).1
  let Zl : Fin M × (Fin (k + 1) → Y × Y₁) → Y × Y₁ := fun z => z.2 (Fin.last k)
  let Yl : Fin M × (Fin (k + 1) → Y × Y₁) → Y := fun z => (Zl z).1
  let Mv : Fin M × (Fin (k + 1) → Y × Y₁) → Fin M := Prod.fst
  have h1 : I[Mv : rcY ; μ] = I[Mv : pair Yl Yp ; μ] :=
    mutualInfo_congr_right hμ Mv (fun v : Y × (Fin k → Y) => (Fin.snoc v.2 v.1 : Fin (k + 1) → Y))
      (fun a b hab => by
        have := snoc_injective2 (α := Y) k (a₁ := (a.2, a.1)) (a₂ := (b.2, b.1)) hab
        simp only [Prod.mk.injEq] at this
        exact Prod.ext this.2 this.1)
      fun z => by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [rcY, Yl, Zl]
        · simp [rcY, Yp, Zp, Fin.init]
  have h2 := chain_rule_mutualInfo₂ hμ Mv Yl Yp
  have h3 : I[Mv : Yp ; μ] = I[Prod.fst : rcY ; c.law W k] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    have e : pair Mv Yp = (pair Prod.fst rcY) ∘ fun z => (z.1, Fin.init z.2) := rfl
    rw [e, dist_comp_eq]
    congr 1
    exact dist_fbLaw_init hW k
  have h4 : I[Mv : Yl | Yp ; μ] ≤ H[Yl ; μ] - H[Yl | pair Yp Mv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    linarith [condEntropy_le_entropy hμ Yl Yp]
  have h5 : H[Yl | pair Zp Mv ; μ] ≤ H[Yl | pair Yp Mv ; μ] := by
    have := condEntropy_le_condEntropy_comp hμ Yl (pair Zp Mv)
      (fun t : (Fin k → Y × Y₁) × Fin M => ((fun i => (t.1 i).1 : Fin k → Y), t.2))
    exact this
  have hchan : ∀ (z : (Fin k → Y × Y₁) × Fin M) (y : Y), dist μ (pair (pair Zp Mv) Yl) (z, y) =
      dist μ (pair Zp Mv) z * bcMarg₁ W (c.fbEnc k z.2 z.1) y := by
    intro z y
    rw [show pair (pair Zp Mv) Yl = pair (pair Zp Mv) fun ω => (Zl ω).1 from rfl,
      dist_pair_marg_fst]
    simp_rw [show ∀ y₂, dist μ (pair (pair Zp Mv) Zl) (z, (y, y₂)) =
      dist μ (pair Zp Mv) z * W (c.fbEnc k z.2 z.1) (y, y₂) from fun y₂ =>
        dist_fbLaw_chan hW k z (y, y₂)]
    rw [← mul_sum]
    rfl
  have h6 := entropy_sub_condEntropy_eq_mutualInfoOf
    (fun z : (Fin k → Y × Y₁) × Fin M => c.fbEnc k z.2 z.1) hμ hW.bcMarg₁ hchan
  have h7 : mutualInfoOf (dist μ ((fun z : (Fin k → Y × Y₁) × Fin M => c.fbEnc k z.2 z.1) ∘
      pair Zp Mv)) (bcMarg₁ W) = rcMacInfo (c.letter W k) W := rfl
  have h1' : I[Prod.fst : rcY ; μ] = I[Mv : rcY ; μ] := rfl
  rw [h1', h1, h2, h3]
  linarith

omit [Fintype X] [Fintype X₁] in
/-- The law of the inputs and of the output at time `k`. -/
lemma RCFBCode.dist_input_output (c : RCFBCode M n X X₁ Y Y₁) (hW : IsChannel W) (k : ℕ) :
    dist (c.law W (k + 1)) (pair (fun z => c.fbEnc k z.1 (Fin.init z.2))
      fun z => z.2 (Fin.last k)) = jointOf (c.letter W k) W := by
  classical
  funext ⟨a, b⟩
  set μ := c.law W (k + 1)
  let Zp : Fin M × (Fin (k + 1) → Y × Y₁) → (Fin k → Y × Y₁) × Fin M := pair (fun z => Fin.init z.2)
    Prod.fst
  let f : (Fin k → Y × Y₁) × Fin M → X × X₁ := fun z => c.fbEnc k z.2 z.1
  have hchan := dist_fbLaw_chan (ν := uniformPMF (Fin M)) (enc := c.fbEnc) hW k
  have e₁ : pair (fun z : Fin M × (Fin (k + 1) → Y × Y₁) => c.fbEnc k z.1 (Fin.init z.2))
      (fun z => z.2 (Fin.last k)) =
      (fun t : ((Fin k → Y × Y₁) × Fin M) × (Y × Y₁) => (f t.1, t.2)) ∘
        pair Zp fun z => z.2 (Fin.last k) := rfl
  have e₂ : (fun z : Fin M × (Fin (k + 1) → Y × Y₁) => c.fbEnc k z.1 (Fin.init z.2)) = f ∘ Zp := rfl
  rw [e₁, dist_comp, jointOf, RCFBCode.letter, e₂, dist_comp, sum_mul, Fintype.sum_prod_type]
  refine sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single b]
  · by_cases hz : f z = a
    · subst hz
      simp only [ite_true]
      exact hchan z b
    · simp [hz]
  · intro b' _ hb'
    refine ite_eq_right fun h => hb' ?_
    exact (Prod.ext_iff.mp h).2
  · simp

/-- `I(M; Yᵏ⁺¹, Y₁ᵏ⁺¹) ≤ I(M; Yᵏ, Y₁ᵏ) + I(Xₖ; Yₖ, Y₁ₖ | X₁ₖ)`, page 17-7 of [elgamal2010]. -/
theorem RCFBCode.mutualInfo_succ_le_bc (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M) (hW : IsChannel W)
    (k : ℕ) :
    I[Prod.fst : Prod.snd ; c.law W (k + 1)] ≤
      I[Prod.fst : Prod.snd ; c.law W k] + rcBcInfo (c.letter W k) W := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set μ := c.law W (k + 1) with hμdef
  have hμ : IsPMF μ := c.law_isPMF hM hW (k + 1)
  have hp := c.letter_isPMF hM hW k
  let Zp : Fin M × (Fin (k + 1) → Y × Y₁) → (Fin k → Y × Y₁) := fun z => Fin.init z.2
  let Zl : Fin M × (Fin (k + 1) → Y × Y₁) → Y × Y₁ := fun z => z.2 (Fin.last k)
  let Mv : Fin M × (Fin (k + 1) → Y × Y₁) → Fin M := Prod.fst
  have h1 : I[Mv : Prod.snd ; μ] = I[Mv : pair Zl Zp ; μ] :=
    mutualInfo_congr_right hμ Mv
      (fun v : (Y × Y₁) × (Fin k → Y × Y₁) => (Fin.snoc v.2 v.1 : Fin (k + 1) → Y × Y₁))
      (fun a b hab => by
        have := snoc_injective2 (α := Y × Y₁) k (a₁ := (a.2, a.1)) (a₂ := (b.2, b.1)) hab
        simp only [Prod.mk.injEq] at this
        exact Prod.ext this.2 this.1)
      fun z => by simp [Zl, Zp, Fin.snoc_init_self]
  have h2 := chain_rule_mutualInfo₂ hμ Mv Zl Zp
  have h3 : I[Mv : Zp ; μ] = I[Prod.fst : Prod.snd ; c.law W k] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [dist_pair_fst_snd]
    exact dist_fbLaw_init hW k
  have h4 : I[Mv : Zl | Zp ; μ] = H[Zl | Zp ; μ] - H[Zl | pair Zp Mv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
  -- the relay input is a function of the past
  let X1k : Fin M × (Fin (k + 1) → Y × Y₁) → X₁ := fun z => (c.fbEnc k z.1 (Fin.init z.2)).2
  have h5 : H[Zl | Zp ; μ] ≤ H[Zl | X1k ; μ] :=
    condEntropy_le_condEntropy_comp hμ Zl Zp fun u => c.relay k u
  -- the two terms of the single-letter expression
  have hd := c.dist_input_output hW k
  have h6 : H[Zl | X1k ; μ] =
      H[Prod.snd | fun z : (X × X₁) × (Y × Y₁) => z.1.2 ; jointOf (c.letter W k) W] := by
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hp hW) ?_
    rw [← hd]
    have e : pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) Prod.snd ∘
        pair (fun z : Fin M × (Fin (k + 1) → Y × Y₁) => c.fbEnc k z.1 (Fin.init z.2))
          (fun z => z.2 (Fin.last k)) = pair X1k Zl := rfl
    rw [← e, dist_comp_eq]
  have hchan : ∀ (z : (Fin k → Y × Y₁) × Fin M) (b : Y × Y₁),
      dist μ (pair (pair Zp Mv) Zl) (z, b) = dist μ (pair Zp Mv) z * W (c.fbEnc k z.2 z.1) b :=
    fun z b => dist_fbLaw_chan hW k z b
  have h7 := condEntropy_of_channel (fun z : (Fin k → Y × Y₁) × Fin M => c.fbEnc k z.2 z.1) hchan
  have h8 : ∑ a, dist μ ((fun z : (Fin k → Y × Y₁) × Fin M => c.fbEnc k z.2 z.1) ∘ pair Zp Mv) a *
      entropy (W a) = ∑ a, c.letter W k a * entropy (W a) := rfl
  have h9 := rcBcInfo_eq hp hW
  have h1' : I[Prod.fst : Prod.snd ; μ] = I[Mv : Prod.snd ; μ] := rfl
  rw [h1', h1, h2, h3]
  linarith

end Step

/-! ### The cutset bound -/

section Cutset

variable [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁] {M n : ℕ}
  {W : X × X₁ → Y × Y₁ → ℝ}

/-- **Theorem 1 of Lecture 17 of [elgamal2010], page 17-5.** The cutset bound
`max_{p(x, x₁)} min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)}`, in nats. -/
def rcCutsetBound (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  sSup {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧ v = min (rcMacInfo p W) (rcBcInfo p W)}

lemma mutualInfo_rcY_le_sum (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M) (hW : IsChannel W) (k : ℕ) :
    I[Prod.fst : rcY ; c.law W k] ≤ ∑ i ∈ range k, rcMacInfo (c.letter W i) W := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  induction k with
  | zero =>
    have hμ := c.law_isPMF hM hW 0
    rw [mutualInfo_eq_entropy_sub_condEntropy' hμ]
    have h1 := entropyRV_le_log_card hμ (rcY : Fin M × (Fin 0 → Y × Y₁) → Fin 0 → Y)
    have h2 := condEntropy_nonneg hμ (rcY : Fin M × (Fin 0 → Y × Y₁) → Fin 0 → Y) Prod.fst
    simp only [Fintype.card_unique, Nat.cast_one, log_one] at h1
    simp only [range_zero, sum_empty]
    linarith
  | succ k ih =>
    rw [sum_range_succ]
    linarith [c.mutualInfo_succ_le_mac hM hW k]

lemma mutualInfo_law_le_sum (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M) (hW : IsChannel W) (k : ℕ) :
    I[Prod.fst : Prod.snd ; c.law W k] ≤ ∑ i ∈ range k, rcBcInfo (c.letter W i) W := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  induction k with
  | zero =>
    have hμ := c.law_isPMF hM hW 0
    rw [mutualInfo_eq_entropy_sub_condEntropy' hμ]
    have h1 := entropyRV_le_log_card hμ (Prod.snd : Fin M × (Fin 0 → Y × Y₁) → Fin 0 → Y × Y₁)
    have h2 := condEntropy_nonneg hμ (Prod.snd : Fin M × (Fin 0 → Y × Y₁) → Fin 0 → Y × Y₁) Prod.fst
    simp only [Fintype.card_unique, Nat.cast_one, log_one] at h1
    simp only [range_zero, sum_empty]
    linarith
  | succ k ih =>
    rw [sum_range_succ]
    linarith [c.mutualInfo_succ_le_bc hM hW k]

/-- **Pages 17-6 to 17-8 of [elgamal2010].** For every code there is an input law with
`(1 - P_e) log M ≤ log 2 + n min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)}`. -/
theorem RCFBCode.one_sub_errProb_mul_log_le (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M) (hn : 0 < n)
    (hW : IsChannel W) :
    ∃ p : X × X₁ → ℝ, IsPMF p ∧ (1 - c.errProb W) * log M ≤
      log 2 + n * min (rcMacInfo p W) (rcBcInfo p W) := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hμ := c.law_isPMF hM hW n
  have hq : ∀ i : Fin n, IsPMF (c.letter W i) := fun i => c.letter_isPMF hM hW i
  let w : Fin n → ℝ := uniformPMF (Fin n)
  have hw : IsPMF w := uniformPMF_isPMF
  have hwv : ∀ i, w i = 1 / n := fun i => by simp [w, uniformPMF]
  let p : X × X₁ → ℝ := fun a => ∑ i : Fin n, w i * c.letter W i a
  have hp : IsPMF p := by
    refine ⟨fun a => sum_nonneg fun i _ => mul_nonneg (hw.nonneg i) ((hq i).nonneg a), ?_⟩
    simp only [p]
    rw [sum_comm]
    simp_rw [← mul_sum, (hq _).sum_eq_one, mul_one, hw.sum_eq_one]
  refine ⟨p, hp, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- Fano's inequality
  have hF := fano_weak hμ Prod.fst rcY c.dec
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ
    (Prod.fst : Fin M × (Fin n → Y × Y₁) → Fin M) rcY
  have hH : H[Prod.fst ; c.law W n] = log M := by
    have hd : dist (c.law W n) Prod.fst = uniformPMF (Fin M) := dist_fst_fbLaw hW n
    rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_fin]
  have hcard : (Fintype.card (Fin M) : ℝ) = M := by simp
  have hbase : (1 - c.errProb W) * log M ≤ log 2 + I[Prod.fst : rcY ; c.law W n] := by
    have : InfoTheory.errProb (c.law W n) Prod.fst rcY c.dec = c.errProb W := rfl
    rw [this, hcard] at hF
    linarith
  -- the two cuts
  have hsum : ∀ g : ℕ → ℝ, ∑ i ∈ range n, g i = n * ∑ i : Fin n, w i * g i := by
    intro g
    rw [← Fin.sum_univ_eq_sum_range, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hwv]
    field_simp
  have hmac : I[Prod.fst : rcY ; c.law W n] ≤ n * rcMacInfo p W := by
    refine (mutualInfo_rcY_le_sum c hM hW n).trans ?_
    have hcon := (mutualInfoOf_concave_input hW.bcMarg₁).le_map_sum (t := univ) (w := w)
      (p := fun i : Fin n => c.letter W i) (fun i _ => hw.nonneg i) hw.sum_eq_one fun i _ => hq i
    have e : (∑ i, w i • c.letter W i) = p := by
      funext a
      simp [p, Finset.sum_apply]
    rw [e] at hcon
    simp only [smul_eq_mul] at hcon
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hcon hn'.le
  have hbc : I[Prod.fst : rcY ; c.law W n] ≤ n * rcBcInfo p W := by
    have hle : I[Prod.fst : rcY ; c.law W n] ≤ I[Prod.fst : Prod.snd ; c.law W n] :=
      mutualInfo_comp_le hμ Prod.fst Prod.snd fun z i => (z i).1
    refine hle.trans ((mutualInfo_law_le_sum c hM hW n).trans ?_)
    have hcon := sum_rcBcInfo_le hw hq hW
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hcon hn'.le
  refine hbase.trans (add_le_add le_rfl ?_)
  rw [mul_min_of_nonneg _ _ hn'.le]
  exact le_min hmac hbc

omit [Fintype X] [Fintype X₁] in
/-- **Fano's inequality for a code of the relay channel.** -/
lemma RCFBCode.one_sub_errProb_mul_log_le_info (c : RCFBCode M n X X₁ Y Y₁) (hM : 0 < M)
    (hW : IsChannel W) :
    (1 - c.errProb W) * log M ≤ log 2 + I[Prod.fst : rcY ; c.law W n] := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hμ := c.law_isPMF hM hW n
  have hF := fano_weak hμ Prod.fst rcY c.dec
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ
    (Prod.fst : Fin M × (Fin n → Y × Y₁) → Fin M) rcY
  have hH : H[Prod.fst ; c.law W n] = log M := by
    have hd : dist (c.law W n) Prod.fst = uniformPMF (Fin M) := dist_fst_fbLaw hW n
    rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_fin]
  have hcard : (Fintype.card (Fin M) : ℝ) = M := by simp
  have : InfoTheory.errProb (c.law W n) Prod.fst rcY c.dec = c.errProb W := rfl
  rw [this, hcard] at hF
  linarith

/-- The values in the cutset bound are bounded. -/
lemma bddAbove_rcCutset (hW : IsChannel W) :
    BddAbove {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧ v = min (rcMacInfo p W) (rcBcInfo p W)} := by
  refine ⟨capacity (bcMarg₁ W), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact (min_le_left _ _).trans (mutualInfoOf_le_capacity hp hW.bcMarg₁)

/-- **Fano's inequality and the cutset bound for a code of the relay channel without feedback.** -/
theorem RCCode.one_sub_errProb_mul_log_le (c : RCCode M n X X₁ Y Y₁) (hM : 0 < M) (hn : 0 < n)
    (hW : IsChannel W) :
    ∃ p : X × X₁ → ℝ, IsPMF p ∧ (1 - c.errProb W) * log M ≤
      log 2 + n * min (rcMacInfo p W) (rcBcInfo p W) :=
  c.toFB.one_sub_errProb_mul_log_le hM hn hW

omit [Fintype X] [Fintype X₁] in
lemma RCCode.law_isPMF (c : RCCode M n X X₁ Y Y₁) (hM : 0 < M) (hW : IsChannel W) (k : ℕ) :
    IsPMF (c.law W k) :=
  c.toFB.law_isPMF hM hW k

omit [Fintype X] [Fintype X₁] in
/-- **Fano's inequality for a code of the relay channel.** -/
lemma RCCode.one_sub_errProb_mul_log_le_info (c : RCCode M n X X₁ Y Y₁) (hM : 0 < M)
    (hW : IsChannel W) :
    (1 - c.errProb W) * log M ≤ log 2 + I[Prod.fst : rcY ; c.law W n] :=
  c.toFB.one_sub_errProb_mul_log_le_info hM hW

omit [Fintype X] [Fintype X₁] in
/-- A rate achievable without feedback is achievable with feedback. -/
lemma IsAchievableRC.toFB {R : ℝ} (h : IsAchievableRC W R) : IsAchievableRCFB W R := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun n => (c n).toFB, hc⟩

/-- **The cutset bound holds with feedback, pages 17-5 and 18-44 of [elgamal2010].** Every
achievable rate, converted to nats, is at most the cutset bound. -/
theorem IsAchievableRCFB.le_rcCutsetBound (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRCFB W R) : R * log 2 ≤ rcCutsetBound W := by
  obtain ⟨c, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R⌉₊ := fun n => by positivity
  have hP1 : ∀ n, (c n).errProb W ≤ 1 := fun n => by
    have : Nonempty (Fin (2 ^ ⌈(n : ℝ) * R⌉₊)) := ⟨⟨0, hpos n⟩⟩
    exact errProb_le_one ((c n).law_isPMF (hpos n) hW n) _ _ _
  refine le_of_converse_bound hc hP1 fun n hn => ?_
  obtain ⟨p, hp, hle⟩ := (c n).one_sub_errProb_mul_log_le (hpos n) hn hW
  have hval : min (rcMacInfo p W) (rcBcInfo p W) ≤ rcCutsetBound W :=
    le_csSup (bddAbove_rcCutset hW) ⟨p, hp, rfl⟩
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hceil : (⌈exp (n * (R * log 2))⌉₊ : ℝ) ≤ ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by
    have hle₂ : exp (n * (R * log 2)) ≤ ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by
      push_cast
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine exp_le_exp.mpr ?_
      have := Nat.le_ceil ((n : ℝ) * R)
      have hl : 0 < log 2 := log_pos (by norm_num)
      nlinarith
    exact_mod_cast Nat.ceil_le.mpr hle₂
  have hexp : (0 : ℝ) < ⌈exp (n * (R * log 2))⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr (exp_pos _)
  have hlog := log_le_log hexp hceil
  have h1 : 0 ≤ 1 - (c n).errProb W := sub_nonneg.mpr (hP1 n)
  calc _ ≤ (1 - (c n).errProb W) * log ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog h1
    _ ≤ _ := hle
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hval hn'
        linarith

/-- **Theorem 1 of Lecture 17 of [elgamal2010], page 17-5: the cutset bound.** Every achievable
rate, converted to nats, is at most the cutset bound. -/
theorem IsAchievableRC.le_rcCutsetBound (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableRC W R) : R * log 2 ≤ rcCutsetBound W :=
  h.toFB.le_rcCutsetBound hW

omit [Fintype X] [Fintype X₁] in
/-- **A converse from a bound on the information.** If `I(M; Yⁿ) ≤ n V` for all the codes, then
every achievable rate, converted to nats, is at most `V`. -/
theorem IsAchievableRC.le_of_info_bound {R V : ℝ} (hW : IsChannel W) (h : IsAchievableRC W R)
    (hV : ∀ (n : ℕ) (_ : 0 < n) (c : RCCode (2 ^ ⌈(n : ℝ) * R⌉₊) n X X₁ Y Y₁),
      I[Prod.fst : rcY ; c.law W n] ≤ n * V) : R * log 2 ≤ V := by
  obtain ⟨c, hc⟩ := h
  have hpos : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R⌉₊ := fun n => by positivity
  have hP1 : ∀ n, (c n).errProb W ≤ 1 := fun n => by
    have : Nonempty (Fin (2 ^ ⌈(n : ℝ) * R⌉₊)) := ⟨⟨0, hpos n⟩⟩
    exact errProb_le_one ((c n).law_isPMF (hpos n) hW n) _ _ _
  refine le_of_converse_bound hc hP1 fun n hn => ?_
  have hle := (c n).one_sub_errProb_mul_log_le_info (hpos n) hW
  have hceil : (⌈exp (n * (R * log 2))⌉₊ : ℝ) ≤ ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by
    have hle₂ : exp (n * (R * log 2)) ≤ ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) := by
      push_cast
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      refine exp_le_exp.mpr ?_
      have := Nat.le_ceil ((n : ℝ) * R)
      have hl : 0 < log 2 := log_pos (by norm_num)
      nlinarith
    exact_mod_cast Nat.ceil_le.mpr hle₂
  have hexp : (0 : ℝ) < ⌈exp (n * (R * log 2))⌉₊ := by
    exact_mod_cast Nat.ceil_pos.mpr (exp_pos _)
  have hlog := log_le_log hexp hceil
  have h1 : 0 ≤ 1 - (c n).errProb W := sub_nonneg.mpr (hP1 n)
  calc _ ≤ (1 - (c n).errProb W) * log ((2 ^ ⌈(n : ℝ) * R⌉₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog h1
    _ ≤ _ := hle
    _ ≤ _ := add_le_add le_rfl (hV n hn (c n))

end Cutset

end InfoTheory
