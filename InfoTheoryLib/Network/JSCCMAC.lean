/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.JSCCMACLaw

/-!
# Joint source–channel coding over a MAC: the coding theorem

This file proves Theorem 2 of Lecture 15 of El Gamal and Kim: a 2-DMS `(U₁, U₂)` with a common
function `U₀ = g₁(U₁) = g₂(U₂)` can be sent losslessly over a DM-MAC if
`H(U₁|U₂) < I(X₁; Y|X₂, U₂, W)`, `H(U₂|U₁) < I(X₂; Y|X₁, U₁, W)`,
`H(U₁, U₂|U₀) < I(X₁, X₂; Y|U₀, W)` and `H(U₁, U₂) < I(X₁, X₂; Y)` for some
`p(w) p(x₁|u₁, w) p(x₂|u₂, w)`. Theorem 1 is the special case of a constant `U₀`, with `W = Q`.

## Main definitions

* `MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β`: the joint source–channel codes, and `MACJSCCCode.errProb`.
* `IsLosslessMAC P W`: the sources can be sent losslessly.

## Main statements

* `sum_all_eq`: the law of the sequences.
* `event_a`, `event_b`, `event_c`, `event_d`: the bounds on the four error events.
* `isLosslessMAC_of_lt`: **Theorem 2**.
* `isLosslessMAC_of_lt_time`: **Theorem 1**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ ω ξ₁ ξ₂ β c : Type*}

/-! ### The codes -/

/-- **Lecture 15 of [elgamal2010], page 15-3.** A joint source–channel code of rate pair `(1, 1)`
for a 2-DMS over a DM-MAC. -/
structure MACJSCCCode (n : ℕ) (α₁ α₂ ξ₁ ξ₂ β : Type*) where
  /-- The encoder of the first source. -/
  enc₁ : (Fin n → α₁) → Fin n → ξ₁
  /-- The encoder of the second source. -/
  enc₂ : (Fin n → α₂) → Fin n → ξ₂
  /-- The decoder. -/
  dec : (Fin n → β) → (Fin n → α₁) × (Fin n → α₂)

section Code

variable [Fintype α₁] [Fintype α₂] [Fintype β] {n : ℕ}

open Classical in
/-- **Lecture 15 of [elgamal2010], page 15-4.** The probability of error of a code. -/
def MACJSCCCode.errProb (C : MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β) (P : α₁ × α₂ → ℝ)
    (W : ξ₁ × ξ₂ → β → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * ∑ y, channelExt W n (zipSeq (C.enc₁ (fstSeq ω)) (C.enc₂ (sndSeq ω))) y *
    (if C.dec y = (fstSeq ω, sndSeq ω) then 0 else 1)

/-- **Lecture 15 of [elgamal2010], page 15-4.** The sources are transmitted losslessly over the
DM-MAC if there is a sequence of codes with `P_e → 0`. -/
def IsLosslessMAC (P : α₁ × α₂ → ℝ) (W : ξ₁ × ξ₂ → β → ℝ) : Prop :=
  ∃ C : ∀ n : ℕ, MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β, Tendsto (fun n => (C n).errProb P W) atTop (𝓝 0)

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
instance MACJSCCCode.finite [Finite α₁] [Finite α₂] [Finite ξ₁] [Finite ξ₂] [Finite β] :
    Finite (MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β) :=
  Finite.of_injective (fun C : MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β => (C.enc₁, C.enc₂, C.dec))
    fun C C' h => by
      cases C
      cases C'
      simpa using h

lemma MACJSCCCode.errProb_nonneg {P : α₁ × α₂ → ℝ} {W : ξ₁ × ξ₂ → β → ℝ} (hP : IsPMF P)
    (hW : IsChannel W) (C : MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β) : 0 ≤ C.errProb P W :=
  sum_nonneg fun ω _ => mul_nonneg ((iidPMF_isPMF hP n).nonneg ω) (sum_nonneg fun y _ =>
    mul_nonneg (prod_nonneg fun i _ => (hW _).nonneg _) (by split_ifs <;> norm_num))

/-- To show that the sources can be sent losslessly it is enough to find, for every `ε > 0` and all
large `n`, a code with error probability at most `ε`. -/
theorem isLosslessMAC_of_eventually [Finite ξ₁] [Finite ξ₂] [Nonempty α₁] [Nonempty α₂]
    [Nonempty ξ₁] [Nonempty ξ₂] [Nonempty β] {P : α₁ × α₂ → ℝ} {W : ξ₁ × ξ₂ → β → ℝ} (hP : IsPMF P)
    (hW : IsChannel W)
    (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ C : MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β, C.errProb P W ≤ ε) :
    IsLosslessMAC P W := by
  have hne : ∀ n : ℕ, Nonempty (MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β) := fun n =>
    ⟨⟨fun _ _ => Classical.arbitrary _, fun _ _ => Classical.arbitrary _,
      fun _ => (fun _ => Classical.arbitrary _, fun _ => Classical.arbitrary _)⟩⟩
  obtain ⟨C, hC⟩ := exists_seq_of_eventually
    (C := fun n : ℕ => MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β)
    (fun n C => C.errProb P W) (a := 0) fun ε hε => by
      filter_upwards [h ε hε] with n ⟨C, hC⟩
      exact ⟨C, by rwa [zero_add]⟩
  refine ⟨C, tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (MACJSCCCode.errProb_nonneg hP hW _), fun a ha => ?_⟩⟩
  filter_upwards [hC (a / 2) (by positivity)] with n hn
  rw [zero_add] at hn
  linarith

end Code

/-! ### Sequences -/

section Seq

variable {n : ℕ}

/-- A sum over the sequences of pairs is a sum over the pairs of sequences. -/
lemma sum_zip {a b : Type*} [Fintype a] [Fintype b] (F : (Fin n → a × b) → ℝ) :
    ∑ z, F z = ∑ x, ∑ y, F (zipSeq x y) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    ⟨fun z => (fun i => (z i).1, fun i => (z i).2), fun p i => (p.1 i, p.2 i), fun _ => rfl,
      fun _ => rfl⟩ _ _ fun z => rfl

/-- The sequence of all the variables. -/
def jsSeq (u₁ : Fin n → α₁) (u₂ : Fin n → α₂) (s : Fin n → ω) (a : Fin n → ξ₁) (b : Fin n → ξ₂)
    (y : Fin n → β) : Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β :=
  zipSeq (zipSeq (zipSeq (zipSeq (zipSeq u₁ u₂) s) a) b) y

/-- The law of a pair of source sequences. -/
def jsQ (P : α₁ × α₂ → ℝ) (n : ℕ) (p : (Fin n → α₁) × (Fin n → α₂)) : ℝ :=
  iidPMF P n (zipSeq p.1 p.2)

/-- The conditional law of a sequence given a pair of sequences. -/
def jsA {a b d : Type*} (κ : a × b → d → ℝ) (n : ℕ) (p : (Fin n → a) × (Fin n → b)) : (Fin n → d)
    → ℝ :=
  channelExt κ n (zipSeq p.1 p.2)

lemma jsA_isChannel {a b d : Type*} [Fintype d] {κ : a × b → d → ℝ} (hκ : IsChannel κ) :
    IsChannel (jsA κ n) := fun p => by
  classical
  refine ⟨fun z => ?_, ?_⟩
  · simp only [jsA, channelExt]
    exact prod_nonneg fun i _ => (hκ _).nonneg _
  simp only [jsA, channelExt]
  rw [← Fintype.prod_sum fun i b' => κ (zipSeq p.1 p.2 i) b']
  exact prod_eq_one fun i _ => (hκ _).sum_eq_one

lemma jsQ_isPMF [Fintype α₁] [Fintype α₂] {P : α₁ × α₂ → ℝ} (hP : IsPMF P) :
    IsPMF (jsQ P n) := by
  have hi := iidPMF_isPMF hP n
  refine ⟨fun p => hi.nonneg _, ?_⟩
  rw [Fintype.sum_prod_type, ← hi.sum_eq_one, sum_zip]
  rfl

variable [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂] [Fintype β]
  {P : α₁ × α₂ → ℝ} {τ : ω → ℝ} {κ₁ : α₁ × ω → ξ₁ → ℝ} {κ₂ : α₂ × ω → ξ₂ → ℝ}
  {W : ξ₁ × ξ₂ → β → ℝ}

/-- The test of the decoder: the sequences are jointly typical. -/
def jsTest (L : JZ α₁ α₂ ω ξ₁ ξ₂ β → ℝ) (n : ℕ) (ε : ℝ) (u₁ : Fin n → α₁) (u₂ : Fin n → α₂)
    (s : Fin n → ω) (a : Fin n → ξ₁) (b : Fin n → ξ₂) (y : Fin n → β) : Prop :=
  open Classical in jsSeq u₁ u₂ s a b y ∈ robustTypicalSet L n ε

/-- **The law of the sequences.** The expectation over the true source sequences, `w`-sequence,
codewords and output sequence is the expectation under the i.i.d. law. -/
theorem sum_all_eq (G : (Fin n → α₁) → (Fin n → α₂) → (Fin n → ω) → (Fin n → ξ₁) → (Fin n → ξ₂) →
    (Fin n → β) → ℝ) :
    ∑ u₁, ∑ u₂, jsQ P n (u₁, u₂) * ∑ s, iidPMF τ n s * ∑ a, jsA κ₁ n (u₁, s) a *
        ∑ b, jsA κ₂ n (u₂, s) b * ∑ y, jsA W n (a, b) y * G u₁ u₂ s a b y =
      ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * G (fun i => jU₁ (z i)) (fun i => jU₂ (z i))
        (fun i => jW (z i)) (fun i => jX₁ (z i)) (fun i => jX₂ (z i)) (fun i => jY (z i)) := by
  rw [sum_zip, sum_zip, sum_zip, sum_zip, sum_zip]
  refine sum_congr rfl fun u₁ _ => sum_congr rfl fun u₂ _ => ?_
  simp only [mul_sum]
  refine sum_congr rfl fun s _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
    sum_congr rfl fun y _ => ?_
  have e : iidPMF (jsLaw P τ κ₁ κ₂ W) n
      (zipSeq (zipSeq (zipSeq (zipSeq (zipSeq u₁ u₂) s) a) b) y) =
      jsQ P n (u₁, u₂) * (iidPMF τ n s * (jsA κ₁ n (u₁, s) a * (jsA κ₂ n (u₂, s) b *
        jsA W n (a, b) y))) := by
    simp only [iidPMF, jsQ, jsA, channelExt, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    simp only [jsLaw, jsL₂, jsL₁, jointOf, prodDist, zipSeq]
    ring
  rw [e]
  simp only [zipSeq]
  ring

end Seq

/-! ### Sums over the typical set -/

section Typical

/-- A nonnegative sum over indices, supported on an injective image in the set `T`, is at most
`|T| M` if its terms are at most `M`. -/
lemma sum_typical_le {ι Zs : Type*} [Fintype ι] {w : ι → ℝ} (φ : ι → Zs) (T : Finset Zs) {M : ℝ}
    (hM : 0 ≤ M) (hzero : ∀ x, φ x ∉ T → w x = 0)
    (hinj : ∀ x y, w x ≠ 0 → w y ≠ 0 → φ x = φ y → x = y) (hle : ∀ x, φ x ∈ T → w x ≤ M) :
    ∑ x, w x ≤ T.card * M := by
  classical
  set s := univ.filter fun x => w x ≠ 0 with hs
  have h1 : ∑ x, w x = ∑ x ∈ s, w x := by
    rw [hs, sum_filter]
    refine sum_congr rfl fun x _ => ?_
    by_cases h : w x = 0 <;> simp [h]
  have hmem : ∀ x ∈ s, φ x ∈ T := fun x hx => by
    by_contra h
    exact (mem_filter.1 hx).2 (hzero x h)
  have h2 : ∑ x ∈ s, w x ≤ ∑ _x ∈ s, M := sum_le_sum fun x hx => hle x (hmem x hx)
  have h3 : s.card ≤ T.card := card_le_card_of_injOn φ hmem fun x hx y hy he =>
    hinj x y (mem_filter.1 hx).2 (mem_filter.1 hy).2 he
  rw [h1]
  refine h2.trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h3) hM

/-- The expectation of a function of `R(Zⁿ)` under the i.i.d. law of `Zⁿ`. -/
lemma sum_iid_comp {γ ρ : Type*} [Fintype γ] [Fintype ρ] (L : γ → ℝ) (n : ℕ) (R : γ → ρ)
    (Ψ : (Fin n → ρ) → ℝ) :
    ∑ z, iidPMF L n z * Ψ (fun i => R (z i)) = ∑ r, iidPMF (dist L R) n r * Ψ r := by
  rw [← dist_iidPMF_comp, sum_dist_mul]

variable [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂] [Fintype β] {n : ℕ}
  {ε : ℝ} {P : α₁ × α₂ → ℝ} {τ : ω → ℝ} {κ₁ : α₁ × ω → ξ₁ → ℝ} {κ₂ : α₂ × ω → ξ₂ → ℝ}
  {W : ξ₁ × ξ₂ → β → ℝ}

/-- `μ(ω) ≤ p_X(X(ω))`. -/
lemma le_dist_apply {Ω γ : Type*} [Fintype Ω] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → γ) (x : Ω) :
    μ x ≤ dist μ X (X x) := by
  classical
  have := single_le_sum (f := fun w => if X w = X x then μ w else 0)
    (fun w _ => by
      change 0 ≤ if X w = X x then μ w else 0
      split_ifs
      · exact hμ.nonneg w
      · exact le_rfl) (mem_univ x)
  simpa [dist] using this

variable (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (hW : IsChannel W)

include hP hτ h₁ h₂ hW

/-- The bound on the codeword of a wrong first source sequence. -/
lemma jsA_κ₁_le {z : Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β}
    (hz : z ∈ robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε) :
    jsA κ₁ n (fun i => jU₁ (z i), fun i => jW (z i)) (fun i => jX₁ (z i)) ≤
      exp (-(n * (jsH₁ P τ κ₁ κ₂ W - ε * jsH₁ P τ κ₁ κ₂ W))) := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  refine le_trans (le_of_eq ?_) (prod_condDist_le_of_mem hL (pair jU₁ jW) jX₁ hz)
  simp only [jsA, channelExt]
  refine prod_congr rfl fun i _ => ?_
  have hQ : dist (prodDist P τ) (fun v : (α₁ × α₂) × ω => (v.1.1, v.2)) =
      dist (jsLaw P τ κ₁ κ₂ W) (pair jU₁ jW) :=
    (dist_jsLaw_comp₀ h₁ h₂ hW fun v : (α₁ × α₂) × ω => (v.1.1, v.2)).symm
  have hpos := pos_of_mem_robustTypicalSet hL.nonneg hz i
  have ha := hpos.trans_le (le_dist_apply hL (pair jU₁ jW) (z i))
  exact (condDist_eq_of_dist_pair (dist_jsLaw_κ₁ h₂ hW) hQ ha.ne' _).symm

/-- The bound on the codeword of a wrong second source sequence. -/
lemma jsA_κ₂_le {z : Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β}
    (hz : z ∈ robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε) :
    jsA κ₂ n (fun i => jU₂ (z i), fun i => jW (z i)) (fun i => jX₂ (z i)) ≤
      exp (-(n * (jsH₂ P τ κ₁ κ₂ W - ε * jsH₂ P τ κ₁ κ₂ W))) := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  refine le_trans (le_of_eq ?_) (prod_condDist_le_of_mem hL (pair jU₂ jW) jX₂ hz)
  simp only [jsA, channelExt]
  refine prod_congr rfl fun i _ => ?_
  have hQ : dist (jsL₁ P τ κ₁) (fun v : ((α₁ × α₂) × ω) × ξ₁ => (v.1.1.2, v.1.2)) =
      dist (jsLaw P τ κ₁ κ₂ W) (pair jU₂ jW) := by
    have e : (pair jU₂ jW : JZ α₁ α₂ ω ξ₁ ξ₂ β → _) =
        (fun v : ((α₁ × α₂) × ω) × ξ₁ => (v.1.1.2, v.1.2)) ∘ Prod.fst ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, dist_comp_eq, dist_fst_jsLaw hW, dist_fst_jsL₂ h₂]
  have hpos := pos_of_mem_robustTypicalSet hL.nonneg hz i
  have ha := hpos.trans_le (le_dist_apply hL (pair jU₂ jW) (z i))
  exact (condDist_eq_of_dist_pair (dist_jsLaw_κ₂ hW) hQ ha.ne' _).symm

/-- The bound on the sequence of a wrong common part. -/
lemma iidPMF_τ_le {z : Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β}
    (hz : z ∈ robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε) :
    iidPMF τ n (fun i => jW (z i)) ≤ exp (-(n * (entropy τ - ε * entropy τ))) := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  have hd : dist (jsLaw P τ κ₁ κ₂ W) jW = τ := by
    have e := dist_jsLaw_comp₀ (κ₁ := κ₁) (κ₂ := κ₂) (W := W) (P := P) (τ := τ) h₁ h₂ hW
      (Prod.snd : (α₁ × α₂) × ω → ω)
    refine e.trans ?_
    funext w
    rw [dist_snd]
    simp [prodDist, ← sum_mul, hP.sum_eq_one]
  have h := comp_mem_robustTypicalSet hz jW
  rw [hd] at h
  exact iidPMF_le_of_mem_robustTypicalSet hτ h

omit hP hτ h₁ h₂ hW in
/-- The bound on the law of the visible sequence. -/
lemma iidPMF_dist_le {ρ : Type*} [Fintype ρ] {L : JZ α₁ α₂ ω ξ₁ ξ₂ β → ℝ} (hL : IsPMF L)
    (R : JZ α₁ α₂ ω ξ₁ ξ₂ β → ρ) {z : Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β}
    (hz : z ∈ robustTypicalSet L n ε) :
    iidPMF (dist L R) n (fun i => R (z i)) ≤ exp (-(n * (H[R ; L] - ε * H[R ; L]))) :=
  iidPMF_le_of_mem_robustTypicalSet (hL.dist R) (comp_mem_robustTypicalSet hz R)

end Typical

/-! ### The error events -/

section Events

variable [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂] [Fintype β] {n : ℕ}
  {ε : ℝ} {P : α₁ × α₂ → ℝ} {τ : ω → ℝ} {κ₁ : α₁ × ω → ξ₁ → ℝ} {κ₂ : α₂ × ω → ξ₂ → ℝ}
  {W : ξ₁ × ξ₂ → β → ℝ}

variable (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (hW : IsChannel W)

include hP hτ h₁ h₂ hW

/-- **The error event `E₂` of the notes (Lecture 15, page 15-11).** The bound on a wrong first
source sequence. -/
theorem event_a :
    ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦa (jsA κ₁ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε)
        (fun i => jU₂ (z i)) (fun i => jW (z i)) (fun i => jX₂ (z i)) (fun i => jY (z i)) ≤
      (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε).card *
        (exp (-(n * (H[pair (pair (pair jU₂ jW) jX₂) jY ; jsLaw P τ κ₁ κ₂ W] -
          ε * H[pair (pair (pair jU₂ jW) jX₂) jY ; jsLaw P τ κ₁ κ₂ W]))) *
        exp (-(n * (jsH₁ P τ κ₁ κ₂ W - ε * jsH₁ P τ κ₁ κ₂ W)))) := by
  classical
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  set L := jsLaw P τ κ₁ κ₂ W with hLd
  have hA := jsA_isChannel (n := n) h₁
  set R : JZ α₁ α₂ ω ξ₁ ξ₂ β → ((α₂ × ω) × ξ₂) × β := pair (pair (pair jU₂ jW) jX₂) jY with hR
  set q := dist L R with hq
  have hqP : IsPMF q := hL.dist R
  set Ψ : (Fin n → ((α₂ × ω) × ξ₂) × β) → ℝ := fun r =>
    jsccΦa (jsA κ₁ n) (jsTest L n ε) (fun i => (r i).1.1.1) (fun i => (r i).1.1.2)
      (fun i => (r i).1.2) (fun i => (r i).2) with hΨ
  have e := sum_iid_comp L n R Ψ
  refine le_trans (le_of_eq e) ?_
  set w : (Fin n → ((α₂ × ω) × ξ₂) × β) × (Fin n → α₁) × (Fin n → ξ₁) → ℝ := fun x =>
    iidPMF q n x.1 * (jsA κ₁ n (x.2.1, fun i => (x.1 i).1.1.2) x.2.2 *
      (if jsTest L n ε x.2.1 (fun i => (x.1 i).1.1.1) (fun i => (x.1 i).1.1.2) x.2.2
        (fun i => (x.1 i).1.2) (fun i => (x.1 i).2) then 1 else 0)) with hw
  have hflat : ∑ r, iidPMF q n r * Ψ r = ∑ x, w x := by
    simp only [hΨ, jsccΦa, mul_sum, Fintype.sum_prod_type, hw]
  rw [hflat]
  set φ : (Fin n → ((α₂ × ω) × ξ₂) × β) × (Fin n → α₁) × (Fin n → ξ₁) →
      Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β := fun x =>
    jsSeq x.2.1 (fun i => (x.1 i).1.1.1) (fun i => (x.1 i).1.1.2) x.2.2 (fun i => (x.1 i).1.2)
      (fun i => (x.1 i).2) with hφ
  refine sum_typical_le φ _ (by positivity) (fun x hx => ?_) (fun x y _ _ he => ?_) fun x hx => ?_
  · have : ¬ jsTest L n ε x.2.1 (fun i => (x.1 i).1.1.1) (fun i => (x.1 i).1.1.2) x.2.2
        (fun i => (x.1 i).1.2) (fun i => (x.1 i).2) := hx
    simp [hw, this]
  · have key : ∀ i, φ x i = φ y i := fun i => congrFun he i
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · exact congrArg R (key i)
    · exact congrArg jU₁ (key i)
    · exact congrArg jX₁ (key i)
  · have ht : jsTest L n ε x.2.1 (fun i => (x.1 i).1.1.1) (fun i => (x.1 i).1.1.2) x.2.2
        (fun i => (x.1 i).1.2) (fun i => (x.1 i).2) := hx
    have h1 : iidPMF q n x.1 ≤ _ := iidPMF_dist_le hL R hx
    have h2 := jsA_κ₁_le hP hτ h₁ h₂ hW hx
    have h0 := (hA (x.2.1, fun i => (x.1 i).1.1.2)).nonneg x.2.2
    simp only [hw, ht, ite_true, mul_one]
    exact mul_le_mul h1 h2 h0 (exp_pos _).le

/-- **The error event `E₃` of the notes (Lecture 15, page 15-12).** The bound on a wrong second
source sequence. -/
theorem event_b :
    ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦb (jsA κ₂ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε)
        (fun i => jU₁ (z i)) (fun i => jW (z i)) (fun i => jX₁ (z i)) (fun i => jY (z i)) ≤
      (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε).card *
        (exp (-(n * (H[pair (pair (pair jU₁ jW) jX₁) jY ; jsLaw P τ κ₁ κ₂ W] -
          ε * H[pair (pair (pair jU₁ jW) jX₁) jY ; jsLaw P τ κ₁ κ₂ W]))) *
        exp (-(n * (jsH₂ P τ κ₁ κ₂ W - ε * jsH₂ P τ κ₁ κ₂ W)))) := by
  classical
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  set L := jsLaw P τ κ₁ κ₂ W with hLd
  have hB := jsA_isChannel (n := n) h₂
  set R : JZ α₁ α₂ ω ξ₁ ξ₂ β → ((α₁ × ω) × ξ₁) × β := pair (pair (pair jU₁ jW) jX₁) jY with hR
  set q := dist L R with hq
  set Ψ : (Fin n → ((α₁ × ω) × ξ₁) × β) → ℝ := fun r =>
    jsccΦb (jsA κ₂ n) (jsTest L n ε) (fun i => (r i).1.1.1) (fun i => (r i).1.1.2)
      (fun i => (r i).1.2) (fun i => (r i).2) with hΨ
  have e := sum_iid_comp L n R Ψ
  refine le_trans (le_of_eq e) ?_
  set w : (Fin n → ((α₁ × ω) × ξ₁) × β) × (Fin n → α₂) × (Fin n → ξ₂) → ℝ := fun x =>
    iidPMF q n x.1 * (jsA κ₂ n (x.2.1, fun i => (x.1 i).1.1.2) x.2.2 *
      (if jsTest L n ε (fun i => (x.1 i).1.1.1) x.2.1 (fun i => (x.1 i).1.1.2)
        (fun i => (x.1 i).1.2) x.2.2 (fun i => (x.1 i).2) then 1 else 0)) with hw
  have hflat : ∑ r, iidPMF q n r * Ψ r = ∑ x, w x := by
    simp only [hΨ, jsccΦb, mul_sum, Fintype.sum_prod_type, hw]
  rw [hflat]
  set φ : (Fin n → ((α₁ × ω) × ξ₁) × β) × (Fin n → α₂) × (Fin n → ξ₂) →
      Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β := fun x =>
    jsSeq (fun i => (x.1 i).1.1.1) x.2.1 (fun i => (x.1 i).1.1.2) (fun i => (x.1 i).1.2) x.2.2
      (fun i => (x.1 i).2) with hφ
  refine sum_typical_le φ _ (by positivity) (fun x hx => ?_) (fun x y _ _ he => ?_) fun x hx => ?_
  · have : ¬ jsTest L n ε (fun i => (x.1 i).1.1.1) x.2.1 (fun i => (x.1 i).1.1.2)
        (fun i => (x.1 i).1.2) x.2.2 (fun i => (x.1 i).2) := hx
    simp [hw, this]
  · have key : ∀ i, φ x i = φ y i := fun i => congrFun he i
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
    · exact congrArg R (key i)
    · exact congrArg jU₂ (key i)
    · exact congrArg jX₂ (key i)
  · have ht : jsTest L n ε (fun i => (x.1 i).1.1.1) x.2.1 (fun i => (x.1 i).1.1.2)
        (fun i => (x.1 i).1.2) x.2.2 (fun i => (x.1 i).2) := hx
    have h1 : iidPMF q n x.1 ≤ _ := iidPMF_dist_le hL R hx
    have h2 := jsA_κ₂_le hP hτ h₁ h₂ hW hx
    have h0 := (hB (x.2.1, fun i => (x.1 i).1.1.2)).nonneg x.2.2
    simp only [hw, ht, ite_true, mul_one]
    exact mul_le_mul h1 h2 h0 (exp_pos _).le

/-- **The first part of the error event `E₄` of the notes (Lecture 15, page 15-12).** The bound on
two wrong source sequences with the true common part. -/
theorem event_c [Fintype c] (g : α₁ → c) :
    ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦc (fun u : Fin n → α₁ => fun i => g (u i))
        (jsA κ₁ n) (jsA κ₂ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε)
        (fun i => g (jU₁ (z i))) (fun i => jW (z i)) (fun i => jY (z i)) ≤
      (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε).card *
        (exp (-(n * (H[pair (pair (fun z => g (jU₁ z)) jW) jY ; jsLaw P τ κ₁ κ₂ W] -
          ε * H[pair (pair (fun z => g (jU₁ z)) jW) jY ; jsLaw P τ κ₁ κ₂ W]))) *
        (exp (-(n * (jsH₁ P τ κ₁ κ₂ W - ε * jsH₁ P τ κ₁ κ₂ W))) *
          exp (-(n * (jsH₂ P τ κ₁ κ₂ W - ε * jsH₂ P τ κ₁ κ₂ W))))) := by
  classical
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  set L := jsLaw P τ κ₁ κ₂ W with hLd
  have hA := jsA_isChannel (n := n) h₁
  have hB := jsA_isChannel (n := n) h₂
  set R : JZ α₁ α₂ ω ξ₁ ξ₂ β → (c × ω) × β := pair (pair (fun z => g (jU₁ z)) jW) jY with hR
  set q := dist L R with hq
  set Ψ : (Fin n → (c × ω) × β) → ℝ := fun r =>
    jsccΦc (fun u : Fin n → α₁ => fun i => g (u i)) (jsA κ₁ n) (jsA κ₂ n) (jsTest L n ε)
      (fun i => (r i).1.1) (fun i => (r i).1.2) (fun i => (r i).2) with hΨ
  have e := sum_iid_comp L n R Ψ
  refine le_trans (le_of_eq e) ?_
  set w : (Fin n → (c × ω) × β) × (Fin n → α₁) × (Fin n → α₂) × (Fin n → ξ₁) × (Fin n → ξ₂) → ℝ :=
    fun x => iidPMF q n x.1 * ((if (fun i => g (x.2.1 i)) = (fun i => (x.1 i).1.1) then 1 else 0) *
      (jsA κ₁ n (x.2.1, fun i => (x.1 i).1.2) x.2.2.2.1 *
        (jsA κ₂ n (x.2.2.1, fun i => (x.1 i).1.2) x.2.2.2.2 *
      (if jsTest L n ε x.2.1 x.2.2.1 (fun i => (x.1 i).1.2) x.2.2.2.1 x.2.2.2.2
        (fun i => (x.1 i).2) then 1 else 0)))) with hw
  have hflat : ∑ r, iidPMF q n r * Ψ r = ∑ x, w x := by
    simp only [hΨ, jsccΦc, mul_sum, Fintype.sum_prod_type, hw]
    congr!
  rw [hflat]
  set φ : (Fin n → (c × ω) × β) × (Fin n → α₁) × (Fin n → α₂) × (Fin n → ξ₁) × (Fin n → ξ₂) →
      Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β := fun x =>
    jsSeq x.2.1 x.2.2.1 (fun i => (x.1 i).1.2) x.2.2.2.1 x.2.2.2.2 (fun i => (x.1 i).2) with hφ
  have hgc : ∀ x, w x ≠ 0 → (fun i => g (x.2.1 i)) = (fun i => (x.1 i).1.1) := fun x hx => by
    by_contra h
    exact hx (by simp [hw, h])
  refine sum_typical_le φ _ (by positivity) (fun x hx => ?_) (fun x y hx hy he => ?_) fun x hx => ?_
  · have : ¬ jsTest L n ε x.2.1 x.2.2.1 (fun i => (x.1 i).1.2) x.2.2.2.1 x.2.2.2.2
        (fun i => (x.1 i).2) := hx
    simp [hw, this]
  · have key : ∀ i, φ x i = φ y i := fun i => congrFun he i
    have hgx := hgc x hx
    have hgy := hgc y hy
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (Prod.ext
      (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (funext fun i => ?_))))
    · have e1 : (x.1 i).1.1 = g (x.2.1 i) := (congrFun hgx i).symm
      have e2 : (y.1 i).1.1 = g (y.2.1 i) := (congrFun hgy i).symm
      have e3 : x.2.1 i = y.2.1 i := congrArg jU₁ (key i)
      have e4 : (x.1 i).1.2 = (y.1 i).1.2 := congrArg jW (key i)
      have e5 : (x.1 i).2 = (y.1 i).2 := congrArg jY (key i)
      exact Prod.ext (Prod.ext (by rw [e1, e2, e3]) e4) e5
    · exact congrArg jU₁ (key i)
    · exact congrArg jU₂ (key i)
    · exact congrArg jX₁ (key i)
    · exact congrArg jX₂ (key i)
  · have ht : jsTest L n ε x.2.1 x.2.2.1 (fun i => (x.1 i).1.2) x.2.2.2.1 x.2.2.2.2
        (fun i => (x.1 i).2) := hx
    by_cases hgg : (fun i => g (x.2.1 i)) = (fun i => (x.1 i).1.1)
    · have hx1 : x.1 = fun i => R (φ x i) := by
        funext i
        exact Prod.ext (Prod.ext (congrFun hgg i).symm rfl) rfl
      have h1 : iidPMF q n x.1 ≤ exp (-(n * (H[R ; L] - ε * H[R ; L]))) := by
        rw [hx1]
        exact iidPMF_dist_le hL R hx
      have h2 := jsA_κ₁_le hP hτ h₁ h₂ hW hx
      have h3 := jsA_κ₂_le hP hτ h₁ h₂ hW hx
      have h01 := (hA (x.2.1, fun i => (x.1 i).1.2)).nonneg x.2.2.2.1
      have h02 := (hB (x.2.2.1, fun i => (x.1 i).1.2)).nonneg x.2.2.2.2
      simp only [hw, ht, hgg, ite_true, mul_one, one_mul]
      exact mul_le_mul h1 (mul_le_mul h2 h3 h02 (exp_pos _).le) (mul_nonneg h01 h02) (exp_pos _).le
    · simp only [hw, hgg, ite_false, zero_mul, mul_zero]
      positivity

/-- **The second part of the error event `E₄` of the notes (Lecture 15, page 15-12).** The bound on
two wrong source sequences with a wrong common part. -/
theorem event_d :
    ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦd (iidPMF τ n) (jsA κ₁ n) (jsA κ₂ n)
        (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => jY (z i)) ≤
      (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε).card *
        (exp (-(n * (H[jY ; jsLaw P τ κ₁ κ₂ W] - ε * H[jY ; jsLaw P τ κ₁ κ₂ W]))) *
        (exp (-(n * (entropy τ - ε * entropy τ))) *
        (exp (-(n * (jsH₁ P τ κ₁ κ₂ W - ε * jsH₁ P τ κ₁ κ₂ W))) *
          exp (-(n * (jsH₂ P τ κ₁ κ₂ W - ε * jsH₂ P τ κ₁ κ₂ W)))))) := by
  classical
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  set L := jsLaw P τ κ₁ κ₂ W with hLd
  have hA := jsA_isChannel (n := n) h₁
  have hB := jsA_isChannel (n := n) h₂
  have hτn := iidPMF_isPMF hτ n
  set q := dist L jY with hq
  set Ψ : (Fin n → β) → ℝ := fun y =>
    jsccΦd (iidPMF τ n) (jsA κ₁ n) (jsA κ₂ n) (jsTest L n ε) y with hΨ
  have e := sum_iid_comp L n jY Ψ
  refine le_trans (le_of_eq e) ?_
  set w : (Fin n → β) × (Fin n → α₁) × (Fin n → α₂) × (Fin n → ω) × (Fin n → ξ₁) × (Fin n → ξ₂) →
    ℝ :=
    fun x => iidPMF q n x.1 * (iidPMF τ n x.2.2.2.1 *
      (jsA κ₁ n (x.2.1, x.2.2.2.1) x.2.2.2.2.1 *
        (jsA κ₂ n (x.2.2.1, x.2.2.2.1) x.2.2.2.2.2 *
      (if jsTest L n ε x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 x.1 then 1 else 0)))) with hw
  have hflat : ∑ r, iidPMF q n r * Ψ r = ∑ x, w x := by
    simp only [hΨ, jsccΦd, mul_sum, Fintype.sum_prod_type, hw]
  rw [hflat]
  set φ : (Fin n → β) × (Fin n → α₁) × (Fin n → α₂) × (Fin n → ω) × (Fin n → ξ₁) × (Fin n → ξ₂) →
      Fin n → JZ α₁ α₂ ω ξ₁ ξ₂ β := fun x =>
    jsSeq x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 x.1 with hφ
  refine sum_typical_le φ _ (by positivity) (fun x hx => ?_) (fun x y _ _ he => ?_) fun x hx => ?_
  · have : ¬ jsTest L n ε x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 x.1 := hx
    simp [hw, this]
  · have key : ∀ i, φ x i = φ y i := fun i => congrFun he i
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (Prod.ext
      (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_)
        (funext fun i => ?_)))))
    · exact congrArg jY (key i)
    · exact congrArg jU₁ (key i)
    · exact congrArg jU₂ (key i)
    · exact congrArg jW (key i)
    · exact congrArg jX₁ (key i)
    · exact congrArg jX₂ (key i)
  · have ht : jsTest L n ε x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2 x.1 := hx
    have h1 : iidPMF q n x.1 ≤ _ := iidPMF_dist_le hL jY hx
    have h2 := jsA_κ₁_le hP hτ h₁ h₂ hW hx
    have h3 := jsA_κ₂_le hP hτ h₁ h₂ hW hx
    have h4 := iidPMF_τ_le hP hτ h₁ h₂ hW hx
    have h01 := (hA (x.2.1, x.2.2.2.1)).nonneg x.2.2.2.2.1
    have h02 := (hB (x.2.2.1, x.2.2.2.1)).nonneg x.2.2.2.2.2
    have h03 := hτn.nonneg x.2.2.2.1
    simp only [hw, ht, ite_true, mul_one]
    exact mul_le_mul h1 (mul_le_mul h4 (mul_le_mul h2 h3 h02 (exp_pos _).le)
      (mul_nonneg h01 h02) (exp_pos _).le) (mul_nonneg h03 (mul_nonneg h01 h02)) (exp_pos _).le

/-- The term of the true sequences failing the test. -/
theorem event_true :
    (open Classical in ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z *
        (if z ∈ robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε then (0 : ℝ) else 1)) =
      1 - prob (iidPMF (jsLaw P τ κ₁ κ₂ W) n) (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε) := by
  classical
  have hL := iidPMF_isPMF (jsLaw_isPMF hP hτ h₁ h₂ hW) n
  have hs : ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z *
      (if z ∈ robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε then (0 : ℝ) else 1) +
      prob (iidPMF (jsLaw P τ κ₁ κ₂ W) n) (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε) =
      ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z := by
    rw [prob, ← univ_inter (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε), ← sum_ite_mem,
      ← sum_add_distrib]
    refine sum_congr rfl fun z _ => ?_
    by_cases hz : z ∈ robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε <;> simp [hz]
  rw [hL.sum_eq_one] at hs
  linarith

end Events

/-! ### The coding theorem -/

section Main

variable [Fintype α₁] [Fintype α₂] [Fintype ω] [Fintype ξ₁] [Fintype ξ₂] [Fintype β] [Fintype c]
  {n : ℕ} {P : α₁ × α₂ → ℝ} {τ : ω → ℝ} {κ₁ : α₁ × ω → ξ₁ → ℝ} {κ₂ : α₂ × ω → ξ₂ → ℝ}
  {W : ξ₁ × ξ₂ → β → ℝ}

/-- The product of the size of the typical set and the bounds on the sequences. -/
lemma card_mul_exp_le {L : JZ α₁ α₂ ω ξ₁ ξ₂ β → ℝ} (hL : IsPMF L) {ε H' G : ℝ} (hn : (0 : ℝ) ≤ n)
    {M : ℝ} (hM : M ≤ exp (-(n * (H' - ε * H'))))
    (hG : G + ε * (entropy L + H') ≤ H' - entropy L) (hM0 : 0 ≤ M) :
    ((open Classical in (robustTypicalSet L n ε).card : ℕ) : ℝ) * M ≤ exp (-(n * G)) := by
  classical
  have h := card_robustTypicalSet_le hL n ε
  have h0 : (0 : ℝ) ≤ (robustTypicalSet L n ε).card := Nat.cast_nonneg _
  refine (mul_le_mul h hM hM0 (exp_pos _).le).trans ?_
  rw [← exp_add]
  refine exp_le_exp.2 ?_
  nlinarith [mul_le_mul_of_nonneg_left hG hn]

omit [Fintype c] in
open Classical in
/-- The code for one `n`, with the error probability bounded by the expectations of the test
terms. -/
theorem exists_macCode_le [Finite c] (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁)
    (h₂ : IsChannel κ₂) (hW : IsChannel W) [Nonempty α₁] [Nonempty α₂] {g₁ : α₁ → c}
    {g₂ : α₂ → c} (hg : ∀ a b, P (a, b) ≠ 0 → g₁ a = g₂ b) (ε : ℝ) : ∃ C : MACJSCCCode n α₁ α₂ ξ₁
    ξ₂ β, C.errProb P W ≤ (∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * (if z ∈ robustTypicalSet (jsLaw P τ
    κ₁ κ₂ W) n ε then (0 : ℝ) else 1)) + ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦa (jsA κ₁ n)
    (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => jU₂ (z i)) (fun i => jW (z i))
    (fun i => jX₂ (z i)) (fun i => jY (z i)) + ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦb
    (jsA κ₂ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => jU₁ (z i)) (fun i => jW (z i))
    (fun i => jX₁ (z i)) (fun i => jY (z i)) + ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦc
    (fun u : Fin n → α₁ => fun i => g₁ (u i)) (jsA κ₁ n) (jsA κ₂ n)
    (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => g₁ (jU₁ (z i))) (fun i => jW (z i))
    (fun i => jY (z i)) + ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦd (iidPMF τ n) (jsA κ₁ n)
    (jsA κ₂ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => jY (z i)) := by
  have hQ := jsQ_isPMF (n := n) hP
  have hg' : ∀ (u₁ : Fin n → α₁) (u₂ : Fin n → α₂), jsQ P n (u₁, u₂) ≠ 0 →
      (fun i => g₁ (u₁ i)) = fun i => g₂ (u₂ i) := fun u₁ u₂ h => by
    funext i
    refine hg _ _ fun h0 => h ?_
    exact prod_eq_zero (mem_univ i) h0
  obtain ⟨e₁, e₂, dec, hb⟩ := exists_jscc_code_le (Q := jsQ P n) (τ := iidPMF τ n)
    (A := jsA κ₁ n) (B := jsA κ₂ n) (V := jsA W n) (Test := jsTest (jsLaw P τ κ₁ κ₂ W) n ε)
    (g₁ := fun u : Fin n → α₁ => fun i => g₁ (u i)) (g₂ := fun u : Fin n → α₂ => fun i => g₂ (u i))
    hQ (iidPMF_isPMF hτ n) (jsA_isChannel h₁) (jsA_isChannel h₂) (jsA_isChannel hW) hg'
  refine ⟨⟨e₁, e₂, dec⟩, ?_⟩
  refine le_trans (le_of_eq ?_) (hb.trans (le_of_eq ?_))
  · rw [MACJSCCCode.errProb, sum_zip]
    refine sum_congr rfl fun u₁ _ => sum_congr rfl fun u₂ _ => ?_
    refine congrArg _ (sum_congr rfl fun y _ => ?_)
    exact mul_ite_congr _ _ _ Iff.rfl
  simp only [jsccBound_eq]
  have hall := sum_all_eq (P := P) (τ := τ) (κ₁ := κ₁) (κ₂ := κ₂) (W := W) (n := n)
    (fun u₁ u₂ s a b y => jsccΦ₀ (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) u₁ u₂ s a b y +
      jsccΦa (jsA κ₁ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) u₂ s b y +
      jsccΦb (jsA κ₂ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) u₁ s a y +
      jsccΦc (fun u : Fin n → α₁ => fun i => g₁ (u i)) (jsA κ₁ n) (jsA κ₂ n)
        (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => g₁ (u₁ i)) s y +
      jsccΦd (iidPMF τ n) (jsA κ₁ n) (jsA κ₂ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) y)
  refine hall.trans ?_
  simp only [mul_add, sum_add_distrib]
  congr 4
  refine sum_congr rfl fun z _ => ?_
  congr 1
  exact if_congr Iff.rfl rfl rfl

/-- **Theorem 2 of Lecture 15 of [elgamal2010], page 15-16.** Let `g₁(U₁) = g₂(U₂) = U₀` almost
surely. The 2-DMS `(U₁, U₂)` can be sent losslessly over the DM-MAC if
`H(U₁|U₂) < I(X₁; Y|X₂, U₂, W)`, `H(U₂|U₁) < I(X₂; Y|X₁, U₁, W)`,
`H(U₁, U₂|U₀) < I(X₁, X₂; Y|U₀, W)` and `H(U₁, U₂) < I(X₁, X₂; Y)` for some
`p(w) p(x₁|u₁, w) p(x₂|u₂, w)`. The notes take for `U₀` the common part of the sources. -/
theorem isLosslessMAC_of_lt (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂)
    (hW : IsChannel W) {g₁ : α₁ → c} {g₂ : α₂ → c} (hg : ∀ a b, P (a, b) ≠ 0 → g₁ a = g₂ b)
    (ha : H[jU₁ | jU₂ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₁ : jY | pair jX₂ (pair jU₂ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hb : H[jU₂ | jU₁ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₂ : jY | pair jX₁ (pair jU₁ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hc : H[pair jU₁ jU₂ | (fun z => g₁ (jU₁ z)) ; jsLaw P τ κ₁ κ₂ W] <
      I[pair jX₁ jX₂ : jY | pair (fun z => g₁ (jU₁ z)) jW ; jsLaw P τ κ₁ κ₂ W])
    (hd : H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] < I[pair jX₁ jX₂ : jY ; jsLaw P τ κ₁ κ₂ W]) :
    IsLosslessMAC P W := by
  classical
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  obtain ⟨z₀⟩ : Nonempty (JZ α₁ α₂ ω ξ₁ ξ₂ β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hL)
  have : Nonempty α₁ := ⟨jU₁ z₀⟩
  have : Nonempty α₂ := ⟨jU₂ z₀⟩
  have : Nonempty ξ₁ := ⟨jX₁ z₀⟩
  have : Nonempty ξ₂ := ⟨jX₂ z₀⟩
  have : Nonempty β := ⟨jY z₀⟩
  refine isLosslessMAC_of_eventually hP hW fun θ hθ => ?_
  have gapa := jsGap_a hP hτ h₁ h₂ hW
  have gapb := jsGap_b hP hτ h₁ h₂ hW
  have gapc := jsGap_c hP hτ h₁ h₂ hW (fun p : α₁ × α₂ => g₁ p.1)
  have gapd := jsGap_d hP hτ h₁ h₂ hW
  obtain ⟨Hᵣa, hRa⟩ : ∃ x, x = H[pair (pair (pair jU₂ jW) jX₂) jY ; jsLaw P τ κ₁ κ₂ W] := ⟨_, rfl⟩
  obtain ⟨Hᵣb, hRb⟩ : ∃ x, x = H[pair (pair (pair jU₁ jW) jX₁) jY ; jsLaw P τ κ₁ κ₂ W] := ⟨_, rfl⟩
  obtain ⟨Hᵣc, hRc⟩ : ∃ x, x = H[pair (pair (fun z => g₁ (jU₁ z)) jW) jY ; jsLaw P τ κ₁ κ₂ W] :=
    ⟨_, rfl⟩
  obtain ⟨Hᵣd, hRd⟩ : ∃ x, x = H[jY ; jsLaw P τ κ₁ κ₂ W] := ⟨_, rfl⟩
  obtain ⟨Hₗ, hHL⟩ : ∃ x, x = entropy (jsLaw P τ κ₁ κ₂ W) := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ : ∃ x, x = jsH₁ P τ κ₁ κ₂ W := ⟨_, rfl⟩
  obtain ⟨N₂, hN₂⟩ : ∃ x, x = jsH₂ P τ κ₁ κ₂ W := ⟨_, rfl⟩
  obtain ⟨Nτ, hNτ⟩ : ∃ x, x = entropy τ := ⟨_, rfl⟩
  have n1 : 0 ≤ Hₗ := hHL ▸ entropy_nonneg hL
  have n2 : 0 ≤ Hᵣa := hRa ▸ entropyRV_nonneg hL _
  have n3 : 0 ≤ Hᵣb := hRb ▸ entropyRV_nonneg hL _
  have n4 : 0 ≤ Hᵣc := hRc ▸ entropyRV_nonneg hL _
  have n5 : 0 ≤ Hᵣd := hRd ▸ entropyRV_nonneg hL _
  have n6 : 0 ≤ N₁ := hN₁ ▸ condEntropy_nonneg hL _ _
  have n7 : 0 ≤ N₂ := hN₂ ▸ condEntropy_nonneg hL _ _
  have n8 : 0 ≤ Nτ := hNτ ▸ entropy_nonneg hτ
  -- The margin.
  have g1 : 0 < Hᵣa + N₁ - Hₗ := by
    rw [hRa, hN₁, hHL]
    linarith
  have g2 : 0 < Hᵣb + N₂ - Hₗ := by
    rw [hRb, hN₂, hHL]
    linarith
  have g3 : 0 < Hᵣc + (N₁ + N₂) - Hₗ := by
    rw [hRc, hN₁, hN₂, hHL]
    have e := gapc
    linarith
  have g4 : 0 < Hᵣd + (Nτ + (N₁ + N₂)) - Hₗ := by
    rw [hRd, hNτ, hN₁, hN₂, hHL]
    linarith
  obtain ⟨G, hG0, hG1, hG2, hG3, hG4⟩ : ∃ G > 0, G ≤ Hᵣa + N₁ - Hₗ ∧ G ≤ Hᵣb + N₂ - Hₗ ∧
      G ≤ Hᵣc + (N₁ + N₂) - Hₗ ∧ G ≤ Hᵣd + (Nτ + (N₁ + N₂)) - Hₗ :=
    ⟨min (Hᵣa + N₁ - Hₗ) (min (Hᵣb + N₂ - Hₗ) (min (Hᵣc + (N₁ + N₂) - Hₗ)
      (Hᵣd + (Nτ + (N₁ + N₂)) - Hₗ))),
      lt_min g1 (lt_min g2 (lt_min g3 g4)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨K, hK⟩ : ∃ K, K = Hₗ + Hᵣa + Hᵣb + Hᵣc + Hᵣd + Nτ + N₁ + N₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    linarith
  obtain ⟨ε, hε0, hε1, hεK⟩ := exists_eps_mul_lt hK0 (show 0 < G / 2 by positivity)
  have hp := tendsto_prob_robustTypicalSet hL hε0
  have hp' : Tendsto (fun n : ℕ => 1 - prob (iidPMF (jsLaw P τ κ₁ κ₂ W) n)
      (robustTypicalSet (jsLaw P τ κ₁ κ₂ W) n ε)) atTop (𝓝 0) := by
    simpa using hp.const_sub 1
  have hsmall₁ := (tendsto_order.1 hp').2 (θ / 5) (by positivity)
  have hsmall₂ := (tendsto_order.1 (tendsto_exp_neg_mul_nat
    (show 0 < G / 2 by positivity))).2 (θ / 5) (by positivity)
  filter_upwards [hsmall₁, hsmall₂] with n a0 a1
  obtain ⟨C, hC⟩ := exists_macCode_le (n := n) (ξ₁ := ξ₁) (ξ₂ := ξ₂) (β := β) hP hτ h₁ h₂ hW hg ε
  refine ⟨C, hC.trans ?_⟩
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hε2 : ∀ x : ℝ, 0 ≤ x → x ≤ K → ε * x ≤ G / 2 := fun x h0 hx =>
    (mul_le_mul_of_nonneg_left hx hε0.le).trans hεK.le
  have hexp : ∀ a b : ℝ, exp (-(n * (a - ε * a))) * exp (-(n * (b - ε * b))) =
      exp (-(n * ((a + b) - ε * (a + b)))) := fun a b => by
    rw [← exp_add]
    congr 1
    ring
  have hfin : ∀ {H' : ℝ}, 0 ≤ H' → Hₗ + H' ≤ K → G ≤ H' - Hₗ → G / 2 + ε * (Hₗ + H') ≤ H' - Hₗ :=
    fun {H'} h0 hb' hg' => by
      have := hε2 (Hₗ + H') (by linarith) hb'
      linarith
  -- The four events.
  have ea : ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦa (jsA κ₁ n)
      (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => jU₂ (z i)) (fun i => jW (z i))
      (fun i => jX₂ (z i)) (fun i => jY (z i)) ≤ exp (-(n * (G / 2))) := by
    refine (event_a hP hτ h₁ h₂ hW).trans ?_
    have hG' := hfin (H' := Hᵣa + N₁) (by linarith) (by rw [hK]; linarith) hG1
    rw [hRa, hN₁] at hG'
    rw [hHL] at hG'
    exact card_mul_exp_le hL hn (le_of_eq (hexp _ _)) hG' (by positivity)
  have eb : ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦb (jsA κ₂ n)
      (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => jU₁ (z i)) (fun i => jW (z i))
      (fun i => jX₁ (z i)) (fun i => jY (z i)) ≤ exp (-(n * (G / 2))) := by
    refine (event_b hP hτ h₁ h₂ hW).trans ?_
    have hG' := hfin (H' := Hᵣb + N₂) (by linarith) (by rw [hK]; linarith) hG2
    rw [hRb, hN₂] at hG'
    rw [hHL] at hG'
    exact card_mul_exp_le hL hn (le_of_eq (hexp _ _)) hG' (by positivity)
  have ec : ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦc (fun u : Fin n → α₁ => fun i => g₁ (u i))
      (jsA κ₁ n) (jsA κ₂ n) (jsTest (jsLaw P τ κ₁ κ₂ W) n ε)
      (fun i => g₁ (jU₁ (z i))) (fun i => jW (z i)) (fun i => jY (z i)) ≤
      exp (-(n * (G / 2))) := by
    refine (event_c hP hτ h₁ h₂ hW g₁).trans ?_
    have hG' := hfin (H' := Hᵣc + (N₁ + N₂)) (by linarith) (by rw [hK]; linarith) hG3
    rw [hRc, hN₁, hN₂] at hG'
    rw [hHL] at hG'
    refine card_mul_exp_le hL hn (le_of_eq ?_) hG' (by positivity)
    rw [hexp, hexp]
  have ed : ∑ z, iidPMF (jsLaw P τ κ₁ κ₂ W) n z * jsccΦd (iidPMF τ n) (jsA κ₁ n) (jsA κ₂ n)
      (jsTest (jsLaw P τ κ₁ κ₂ W) n ε) (fun i => jY (z i)) ≤ exp (-(n * (G / 2))) := by
    refine (event_d hP hτ h₁ h₂ hW).trans ?_
    have hG' := hfin (H' := Hᵣd + (Nτ + (N₁ + N₂))) (by linarith) (by rw [hK]; linarith) hG4
    rw [hRd, hNτ, hN₁, hN₂] at hG'
    rw [hHL] at hG'
    refine card_mul_exp_le hL hn (le_of_eq ?_) hG' (by positivity)
    rw [hexp, hexp, hexp]
  have e0 := event_true (n := n) (ε := ε) hP hτ h₁ h₂ hW
  rw [← e0] at a0
  have a1' : exp (-(n * (G / 2))) < θ / 5 := a1
  have hsum : ∀ {a b c d e : ℝ}, a < θ / 5 → b ≤ exp (-(n * (G / 2))) →
      c ≤ exp (-(n * (G / 2))) → d ≤ exp (-(n * (G / 2))) → e ≤ exp (-(n * (G / 2))) →
      a + b + c + d + e ≤ θ := fun h0 h1' h2' h3' h4' => by linarith
  exact hsum (lt_of_eq_of_lt (sum_congr rfl fun _ _ => mul_ite_congr _ _ _ Iff.rfl) a0) ea eb ec ed

/-- **Theorem 1 of Lecture 15 of [elgamal2010], page 15-7.** The 2-DMS `(U₁, U₂)` can be sent
losslessly over the DM-MAC if `H(U₁|U₂) < I(X₁; Y|X₂, U₂, Q)`, `H(U₂|U₁) < I(X₂; Y|X₁, U₁, Q)` and
`H(U₁, U₂) < I(X₁, X₂; Y|Q)` for some `p(q) p(x₁|u₁, q) p(x₂|u₂, q)`. This is Theorem 2 for a
constant common function and `W = Q`, where the time sharing is done by the sequence `wⁿ`. -/
theorem isLosslessMAC_of_lt_time (hP : IsPMF P) (hτ : IsPMF τ) (h₁ : IsChannel κ₁)
    (h₂ : IsChannel κ₂) (hW : IsChannel W)
    (ha : H[jU₁ | jU₂ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₁ : jY | pair jX₂ (pair jU₂ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hb : H[jU₂ | jU₁ ; jsLaw P τ κ₁ κ₂ W] <
      I[jX₂ : jY | pair jX₁ (pair jU₁ jW) ; jsLaw P τ κ₁ κ₂ W])
    (hc : H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] <
      I[pair jX₁ jX₂ : jY | jW ; jsLaw P τ κ₁ κ₂ W]) :
    IsLosslessMAC P W := by
  have hL := jsLaw_isPMF hP hτ h₁ h₂ hW
  refine isLosslessMAC_of_lt (c := Unit) (g₁ := fun _ => ()) (g₂ := fun _ => ()) hP hτ h₁ h₂ hW
    (fun _ _ _ => rfl) ha hb ?_ ?_
  · rw [condEntropy_const hL]
    have e : H[pair jU₁ jU₂ ; jsLaw P τ κ₁ κ₂ W] < _ := hc
    refine lt_of_lt_of_le e (le_of_eq ?_)
    rw [condMutualInfo, condMutualInfo]
    congr 1
    · exact (condEntropy_congr_right hL (pair jX₁ jX₂) (fun w : ω => ((), w))
        (fun a b h => (Prod.mk.inj h).2) fun _ => rfl).symm
    · exact (condEntropy_congr_right hL (pair jX₁ jX₂) (fun t : β × ω => (t.1, (), t.2))
        (fun a b h => by
          obtain ⟨a1, a2⟩ := a
          obtain ⟨b1, b2⟩ := b
          simp only [Prod.mk.injEq, true_and] at h ⊢
          exact h) fun _ => rfl).symm
  · refine lt_of_lt_of_le hc ?_
    rw [condMutualInfo_comm hL, condMutualInfo, mutualInfo_comm hL,
      mutualInfo_eq_entropy_sub_condEntropy hL]
    have e1 := condEntropy_jY_eq hP hτ h₁ h₂ hW (pair (pair jX₁ jX₂) jW) (fun t => t.1)
      (fun _ => rfl) (fun v => ((v.1.2, v.2), v.1.1.2)) fun _ => rfl
    rw [e1]
    have e2 := condEntropy_le_entropy hL jY jW
    linarith

end Main

/-! ### Uncoded transmission -/

section Uncoded

variable [Fintype α₁] [Fintype α₂] [Fintype β] [DecidableEq β] {P : α₁ × α₂ → ℝ}
  {W : ξ₁ × ξ₂ → β → ℝ}

/-- **Lecture 15, page 15-6: uncoded transmission.** If the channel is deterministic with
`Y = f(X₁, X₂)`, and `(u₁, u₂)` can be recovered from `f(e₁(u₁), e₂(u₂))` for every pair of positive
probability, then the sources can be sent losslessly, with no coding. -/
theorem isLosslessMAC_of_uncoded {f : ξ₁ × ξ₂ → β} (hW : ∀ x y, W x y = if y = f x then 1 else 0)
    (e₁ : α₁ → ξ₁) (e₂ : α₂ → ξ₂) (d : β → α₁ × α₂)
    (hd : ∀ z, P z ≠ 0 → d (f (e₁ z.1, e₂ z.2)) = z) : IsLosslessMAC P W := by
  classical
  refine ⟨fun n => ⟨fun u i => e₁ (u i), fun u i => e₂ (u i), fun y =>
    (fun i => (d (y i)).1, fun i => (d (y i)).2)⟩, ?_⟩
  have hzero : ∀ n : ℕ, (⟨fun u i => e₁ (u i), fun u i => e₂ (u i), fun y =>
      (fun i => (d (y i)).1, fun i => (d (y i)).2)⟩ : MACJSCCCode n α₁ α₂ ξ₁ ξ₂ β).errProb P W =
        0 :=
    fun n => by
    refine sum_eq_zero fun ω _ => ?_
    by_cases hω : iidPMF P n ω = 0
    · rw [hω, zero_mul]
    have hne : ∀ i, P (ω i) ≠ 0 := fun i h0 => hω (prod_eq_zero (mem_univ i) h0)
    refine mul_eq_zero_of_right _ (sum_eq_zero fun y _ => ?_)
    by_cases hy : ∀ i, y i = f (e₁ (ω i).1, e₂ (ω i).2)
    · have hdec : (fun i => (d (y i)).1, fun i => (d (y i)).2) = (fstSeq ω, sndSeq ω) := by
        refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
        · change (d (y i)).1 = (ω i).1
          rw [hy i, hd (ω i) (hne i)]
        · change (d (y i)).2 = (ω i).2
          rw [hy i, hd (ω i) (hne i)]
      simp only [hdec, ite_true, mul_zero]
    · push Not at hy
      obtain ⟨i, hi⟩ := hy
      refine mul_eq_zero_of_left (prod_eq_zero (mem_univ i) ?_) _
      rw [hW]
      exact ite_eq_right hi
  simp only [hzero]
  exact tendsto_const_nhds

end Uncoded

end InfoTheory
