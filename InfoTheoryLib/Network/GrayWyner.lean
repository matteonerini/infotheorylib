/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.ZhangBerger

/-!
# The Gray–Wyner system: codes and achievability

A pair of sources `(U₁, U₂)` is described by three indices: `M₀` is received by both decoders, `M₁`
by decoder 1 and `M₂` by decoder 2. Decoder `j` recovers `Uⱼⁿ` losslessly. This file defines the
codes and proves the direct part of Theorem 3 of Lecture 15 of El Gamal and Kim.

## Main definitions

* `GWCode M₀ M₁ M₂ n α₁ α₂`: the codes, and `GWCode.errProb`.
* `IsAchievableGW`, `gwRegion`: the achievable rate triples and the optimal rate region, in bits.
* `gwInfo`, `gwCond₁`, `gwCond₂`: `I(U₁, U₂; V)`, `H(U₁|V)` and `H(U₂|V)`, in nats.

## Main statements

* `exists_index_of_card_le`: an index of a small set of sequences.
* `isAchievableGW_of_lt`: the direct part of the Gray–Wyner theorem.

## Implementation notes

No random binning is needed. Encoder 0 describes `(u₁ⁿ, u₂ⁿ)` by a sequence `vⁿ` of a codebook, and
encoder `j` sends the position of `uⱼⁿ` in the conditionally typical set `T(Uⱼ|vⁿ)`, as on page
15-23 of the notes.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 15
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α₁ α₂ υ : Type*}

/-! ### The codes -/

/-- **Lecture 15 of [elgamal2010], page 15-22.** A code for the Gray–Wyner system: three encoders of
the pair of sequences, and two decoders. -/
structure GWCode (M₀ M₁ M₂ n : ℕ) (α₁ α₂ : Type*) where
  /-- The encoder of the common description. -/
  enc₀ : (Fin n → α₁ × α₂) → Fin M₀
  /-- The encoder of the description for decoder 1. -/
  enc₁ : (Fin n → α₁ × α₂) → Fin M₁
  /-- The encoder of the description for decoder 2. -/
  enc₂ : (Fin n → α₁ × α₂) → Fin M₂
  /-- The first decoder. -/
  dec₁ : Fin M₀ × Fin M₁ → Fin n → α₁
  /-- The second decoder. -/
  dec₂ : Fin M₀ × Fin M₂ → Fin n → α₂

section Code

variable [Fintype α₁] [Fintype α₂] {M₀ M₁ M₂ n : ℕ}

open Classical in
/-- The probability of error `P{(Û₁ⁿ, Û₂ⁿ) ≠ (U₁ⁿ, U₂ⁿ)}` of a code. -/
def GWCode.errProb (c : GWCode M₀ M₁ M₂ n α₁ α₂) (P : α₁ × α₂ → ℝ) : ℝ :=
  ∑ ω, iidPMF P n ω * (if c.dec₁ (c.enc₀ ω, c.enc₁ ω) = fstSeq ω ∧
    c.dec₂ (c.enc₀ ω, c.enc₂ ω) = sndSeq ω then 0 else 1)

/-- **Lecture 15 of [elgamal2010], page 15-22.** A rate triple, in bits, is achievable if there are
`(2^{nR₀}, 2^{nR₁}, 2^{nR₂}, n)` codes with `P_e → 0`. -/
def IsAchievableGW (P : α₁ × α₂ → ℝ) (R₀ R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₀ ∧ 0 ≤ R₁ ∧ 0 ≤ R₂ ∧
    ∃ c : ∀ n : ℕ, GWCode (2 ^ ⌊n * R₀⌋₊) (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂,
      Tendsto (fun n => (c n).errProb P) atTop (𝓝 0)

/-- **Lecture 15 of [elgamal2010], page 15-22.** The optimal rate region: the closure of the set of
the achievable rate triples. -/
def gwRegion (P : α₁ × α₂ → ℝ) : Set (ℝ × ℝ × ℝ) :=
  closure {R | IsAchievableGW P R.1 R.2.1 R.2.2}

omit [Fintype α₁] [Fintype α₂] in
instance GWCode.finite [Finite α₁] [Finite α₂] : Finite (GWCode M₀ M₁ M₂ n α₁ α₂) :=
  Finite.of_injective (fun c : GWCode M₀ M₁ M₂ n α₁ α₂ =>
      (c.enc₀, c.enc₁, c.enc₂, c.dec₁, c.dec₂))
    fun c c' h => by
      cases c
      cases c'
      simpa using h

omit [Fintype α₁] [Fintype α₂] in
lemma GWCode.nonempty [Nonempty α₁] [Nonempty α₂] (h₀ : 0 < M₀) (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    Nonempty (GWCode M₀ M₁ M₂ n α₁ α₂) :=
  ⟨⟨fun _ => ⟨0, h₀⟩, fun _ => ⟨0, h₁⟩, fun _ => ⟨0, h₂⟩, fun _ _ => Classical.arbitrary α₁,
    fun _ _ => Classical.arbitrary α₂⟩⟩

lemma GWCode.errProb_nonneg {P : α₁ × α₂ → ℝ} (hP : IsPMF P) (c : GWCode M₀ M₁ M₂ n α₁ α₂) :
    0 ≤ c.errProb P :=
  sum_nonneg fun ω _ => mul_nonneg ((iidPMF_isPMF hP n).nonneg ω) (by split_ifs <;> norm_num)

/-- To show that a rate triple is achievable it is enough to find, for every `ε > 0` and all large
`n`, a code with error probability at most `ε`. -/
theorem isAchievableGW_of_eventually [Nonempty α₁] [Nonempty α₂] {P : α₁ × α₂ → ℝ} (hP : IsPMF P)
    {R₀ R₁ R₂ : ℝ} (hR₀ : 0 ≤ R₀) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (h : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      ∃ c : GWCode (2 ^ ⌊n * R₀⌋₊) (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂, c.errProb P ≤ ε) :
    IsAchievableGW P R₀ R₁ R₂ := by
  have hne := fun n : ℕ => GWCode.nonempty (α₁ := α₁) (α₂ := α₂) (n := n)
    (M₀ := 2 ^ ⌊n * R₀⌋₊) (M₁ := 2 ^ ⌊n * R₁⌋₊) (M₂ := 2 ^ ⌊n * R₂⌋₊) (by positivity)
    (by positivity) (by positivity)
  obtain ⟨c, hc⟩ := exists_seq_of_eventually
    (C := fun n : ℕ => GWCode (2 ^ ⌊n * R₀⌋₊) (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α₁ α₂)
    (fun n c => c.errProb P) (a := 0) fun ε hε => by
      filter_upwards [h ε hε] with n ⟨c, hc⟩
      exact ⟨c, by rwa [zero_add]⟩
  refine ⟨hR₀, hR₁, hR₂, c, ?_⟩
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le (GWCode.errProb_nonneg hP _), fun a ha => ?_⟩
  filter_upwards [hc (a / 2) (by positivity)] with n hn
  rw [zero_add] at hn
  linarith

end Code

/-! ### The informations -/

section Info

variable [Fintype α₁] [Fintype α₂] [Fintype υ]

/-- `I(U₁, U₂; V)` for `p(v|u₁, u₂)`, in nats. -/
def gwInfo (P : α₁ × α₂ → ℝ) (κ : α₁ × α₂ → υ → ℝ) : ℝ := I[Prod.fst : Prod.snd ; jointOf P κ]

/-- `H(U₁|V)` for `p(v|u₁, u₂)`, in nats. -/
def gwCond₁ (P : α₁ × α₂ → ℝ) (κ : α₁ × α₂ → υ → ℝ) : ℝ :=
  H[fun z : (α₁ × α₂) × υ => z.1.1 | Prod.snd ; jointOf P κ]

/-- `H(U₂|V)` for `p(v|u₁, u₂)`, in nats. -/
def gwCond₂ (P : α₁ × α₂ → ℝ) (κ : α₁ × α₂ → υ → ℝ) : ℝ :=
  H[fun z : (α₁ × α₂) × υ => z.1.2 | Prod.snd ; jointOf P κ]

end Info

/-! ### Indices of small sets -/

section Index

variable {X : Type*}

open Classical in
/-- An index `i` of a set `S` of at most `M` elements with a decoder `d`. -/
theorem exists_index_of_card_le [Nonempty X] (S : Finset X) {M : ℕ} (hM : 0 < M)
    (h : S.card ≤ M) : ∃ (i : X → Fin M) (d : Fin M → X), ∀ u ∈ S, d (i u) = u := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ↥S) (β := Fin M) (by simpa using h)
  refine ⟨fun u => if hu : u ∈ S then e ⟨u, hu⟩ else ⟨0, hM⟩,
    fun m => if hm : ∃ s : ↥S, e s = m then (hm.choose : X) else Classical.arbitrary X,
    fun u hu => ?_⟩
  have hex : ∃ s : ↥S, e s = e ⟨u, hu⟩ := ⟨_, rfl⟩
  simp only [hu, ↓reduceDIte, hex]
  have := e.injective hex.choose_spec
  rw [this]

end Index

/-! ### Achievability -/

section Achievability

variable [Fintype α₁] [Fintype α₂] [Fintype υ] {P : α₁ × α₂ → ℝ} {κ : α₁ × α₂ → υ → ℝ}

/-- The law of `(V, U₁)`. -/
abbrev gwLaw₁ (P : α₁ × α₂ → ℝ) (κ : α₁ × α₂ → υ → ℝ) : υ × α₁ → ℝ :=
  dist (jointOf P κ) fun z => (z.2, z.1.1)

/-- The law of `(V, U₂)`. -/
abbrev gwLaw₂ (P : α₁ × α₂ → ℝ) (κ : α₁ × α₂ → υ → ℝ) : υ × α₂ → ℝ :=
  dist (jointOf P κ) fun z => (z.2, z.1.2)

lemma condEntropy_gwLaw₁ (hP : IsPMF P) (hκ : IsChannel κ) :
    H[Prod.snd | Prod.fst ; gwLaw₁ P κ] = gwCond₁ P κ :=
  (condEntropy_comp_comp (jointOf_isPMF hP hκ) _ Prod.snd Prod.fst).symm

lemma condEntropy_gwLaw₂ (hP : IsPMF P) (hκ : IsChannel κ) :
    H[Prod.snd | Prod.fst ; gwLaw₂ P κ] = gwCond₂ P κ :=
  (condEntropy_comp_comp (jointOf_isPMF hP hκ) _ Prod.snd Prod.fst).symm

open Classical in
/-- The code for one `n`, from a codebook of `vⁿ` sequences that covers the source sequences. -/
theorem exists_gwCode_of_card_le (hP : IsPMF P) (hκ : IsChannel κ) [Nonempty α₁] [Nonempty α₂]
    {n M₀ M₁ M₂ : ℕ} {ε₀ ε η : ℝ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hη : 0 ≤ η)
    (hc₁ : ∀ v : Fin n → υ, (condRobustTypicalSet (gwLaw₁ P κ) ε v).card ≤ M₁)
    (hc₂ : ∀ v : Fin n → υ, (condRobustTypicalSet (gwLaw₂ P κ) ε v).card ≤ M₂)
    (hf : ∀ x ∈ robustTypicalSet P n ε₀,
      ∑ C : Fin M₀ → Fin n → υ, iidPMF (iidPMF (dist (jointOf P κ) Prod.snd) n) M₀ C *
        (if ∀ m, ¬ zipSeq x (C m) ∈ robustTypicalSet (jointOf P κ) n ε then 1 else 0) ≤ η) :
    ∃ c : GWCode M₀ M₁ M₂ n α₁ α₂, c.errProb P ≤
      ∑ x, iidPMF P n x * (if x ∈ robustTypicalSet P n ε₀ then 0 else 1) + η := by
  have hμ := jointOf_isPMF hP hκ
  have hZ : Nonempty (α₁ × α₂) := inferInstance
  obtain ⟨z₀⟩ := hZ
  obtain ⟨u₀, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF (hκ z₀))
  have : Nonempty υ := ⟨u₀⟩
  have : Nonempty (Fin M₀) := ⟨⟨0, hM₀⟩⟩
  -- The choice of the codebook.
  obtain ⟨C', f, hC⟩ := exists_layer (iidPMF_isPMF hP n) (fun _ => ())
    (fun x => x ∈ robustTypicalSet P n ε₀)
    (fun _ => iidPMF (iidPMF (dist (jointOf P κ) Prod.snd) n) M₀)
    (fun _ C x m => zipSeq x (C m) ∈ robustTypicalSet (jointOf P κ) n ε) hη
    fun x hx => ⟨iidPMF_isPMF (iidPMF_isPMF (hμ.dist _) n) M₀,
      le_trans (le_of_eq (sum_congr rfl fun D _ => mul_ite_congr _ _ _ Iff.rfl)) (hf x hx)⟩
  set C := C' () with hCd
  -- The indices.
  choose i₁ d₁ hd₁ using fun v : Fin n → υ =>
    exists_index_of_card_le (condRobustTypicalSet (gwLaw₁ P κ) ε v) hM₁ (hc₁ v)
  choose i₂ d₂ hd₂ using fun v : Fin n → υ =>
    exists_index_of_card_le (condRobustTypicalSet (gwLaw₂ P κ) ε v) hM₂ (hc₂ v)
  refine ⟨⟨f, fun x => i₁ (C (f x)) (fstSeq x), fun x => i₂ (C (f x)) (sndSeq x),
    fun m => d₁ (C m.1) m.2, fun m => d₂ (C m.1) m.2⟩, ?_⟩
  refine le_trans ?_ (hC.trans (le_of_eq ?_))
  · refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ((iidPMF_isPMF hP n).nonneg x)
    by_cases h : x ∈ robustTypicalSet P n ε₀ ∧ zipSeq x (C (f x)) ∈ robustTypicalSet (jointOf P κ) n
      ε
    · have ht₁ : zipSeq (C (f x)) (fstSeq x) ∈ robustTypicalSet (gwLaw₁ P κ) n ε :=
        comp_mem_robustTypicalSet h.2 fun z : (α₁ × α₂) × υ => (z.2, z.1.1)
      have ht₂ : zipSeq (C (f x)) (sndSeq x) ∈ robustTypicalSet (gwLaw₂ P κ) n ε :=
        comp_mem_robustTypicalSet h.2 fun z : (α₁ × α₂) × υ => (z.2, z.1.2)
      have e₁ := hd₁ (C (f x)) (fstSeq x) (mem_condRobustTypicalSet.2 ht₁)
      have e₂ := hd₂ (C (f x)) (sndSeq x) (mem_condRobustTypicalSet.2 ht₂)
      simp only [e₁, e₂, and_self, ite_true]
      simp [h]
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  · congr 1
    exact sum_congr rfl fun x _ => mul_ite_congr _ _ _ Iff.rfl

/-- `e^{na} ≤ 2^⌊nR⌋` for `n` large if `a < R log 2`. -/
lemma eventually_exp_le_two_pow_floor {a R : ℝ} (h : a < R * log 2) :
    ∀ᶠ n : ℕ in atTop, exp (n * a) ≤ ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) * (R * log 2 - a)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 h)
  filter_upwards [hlim.eventually_ge_atTop (log 2)] with n hn
  refine le_trans (exp_le_exp.2 ?_) (exp_le_two_pow_floor n R)
  nlinarith

open Classical in
/-- The codes for all large `n`, for abstract numbers of indices. -/
theorem eventually_gw_code_aux (hP : IsPMF P) (hκ : IsChannel κ) [Nonempty α₁] [Nonempty α₂]
    {M₀ M₁ M₂ : ℕ → ℕ} {ε τ : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2) (hτ : 0 < τ)
    (hM₀ : ∀ n, 0 < M₀ n) (hM₁ : ∀ n, 0 < M₁ n) (hM₂ : ∀ n, 0 < M₂ n)
    (hc₁ : ∀ᶠ n : ℕ in atTop, ∀ v : Fin n → υ, (condRobustTypicalSet (gwLaw₁ P κ) ε v).card ≤ M₁ n)
    (hc₂ : ∀ᶠ n : ℕ in atTop, ∀ v : Fin n → υ, (condRobustTypicalSet (gwLaw₂ P κ) ε v).card ≤ M₂ n)
    (hη : Tendsto (fun n : ℕ => exp (-((M₀ n : ℝ) * ((1 - ε) * exp (-(n * (gwInfo P κ +
      ε * (2 * log (Fintype.card υ))))))))) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∃ c : GWCode (M₀ n) (M₁ n) (M₂ n) n α₁ α₂, c.errProb P ≤ τ := by
  have hμ := jointOf_isPMF hP hκ
  have hX : dist (jointOf P κ) Prod.fst = P := dist_jointOf_fst hκ
  have hpair : dist (jointOf P κ) (pair Prod.fst Prod.snd) = jointOf P κ := dist_pair_fst_snd _
  have hfirst := eventually_sum_first_codebook_le (ε₀ := ε / 2) (ε := ε) hμ Prod.fst Prod.snd
    (by linarith) hε (by linarith)
  have hIc : I[Prod.snd : Prod.fst ; jointOf P κ] = gwInfo P κ := mutualInfo_comm hμ _ _
  rw [hX, hpair, hIc] at hfirst
  have hp := tendsto_sum_ite_not_typical hP (show 0 < ε / 2 by positivity)
  have hsmall : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) → ∀ᶠ n in atTop, f n < τ / 2 := fun h =>
    (tendsto_order.1 h).2 _ (by positivity)
  filter_upwards [hfirst, hc₁, hc₂, hsmall hp, hsmall hη] with n h1' h2' h3' a0 a1
  obtain ⟨c', hc'⟩ := exists_gwCode_of_card_le (ε₀ := ε / 2) (ε := ε) (η := _) hP hκ
    (hM₀ n) (hM₁ n) (hM₂ n) (exp_pos _).le h2' h3'
    (fun x hx => by convert h1' x hx (M₀ n))
  refine ⟨c', hc'.trans ?_⟩
  have hsum : ∀ {a b : ℝ}, a < τ / 2 → b < τ / 2 → a + b ≤ τ := fun h h' => by linarith
  exact hsum (lt_of_eq_of_lt (sum_congr rfl fun _ _ => mul_ite_congr _ _ _ Iff.rfl) a0) a1

/-- A rate is nonnegative if it exceeds a nonnegative number, in nats. -/
lemma nonneg_of_lt_mul_log_two {a R : ℝ} (ha : 0 ≤ a) (h : a < R * log 2) : 0 ≤ R := by
  have hl := log_pos one_lt_two
  by_contra hc
  nlinarith [not_le.1 hc]

/-- A small number `ε`, for a constant `c` and a margin `S`. -/
lemma exists_eps_mul_lt {c S : ℝ} (hc : 0 ≤ c) (hS : 0 < S) :
    ∃ ε > 0, ε ≤ 1 / 2 ∧ ε * c < S := by
  refine ⟨min (1 / 2) (S / (2 * (c + 1))), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  have h1 : min (1 / 2) (S / (2 * (c + 1))) ≤ S / (2 * (c + 1)) := min_le_right _ _
  have h2 : 0 < min (1 / 2) (S / (2 * (c + 1))) :=
    lt_min (by norm_num) (by positivity)
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

/-- **Theorem 3 of Lecture 15 of [elgamal2010], page 15-22: the direct part.** For `p(v|u₁, u₂)`, a
rate triple in bits is achievable if `R₀ > I(U₁, U₂; V)`, `R₁ > H(U₁|V)` and `R₂ > H(U₂|V)`. -/
theorem isAchievableGW_of_lt (hP : IsPMF P) (hκ : IsChannel κ) {R₀ R₁ R₂ : ℝ}
    (h₀ : gwInfo P κ < R₀ * log 2) (h₁ : gwCond₁ P κ < R₁ * log 2)
    (h₂ : gwCond₂ P κ < R₂ * log 2) : IsAchievableGW P R₀ R₁ R₂ := by
  have hμ := jointOf_isPMF hP hκ
  obtain ⟨⟨a₁, a₂⟩⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have : Nonempty α₁ := ⟨a₁⟩
  have : Nonempty α₂ := ⟨a₂⟩
  have hI0 : 0 ≤ gwInfo P κ := mutualInfo_nonneg hμ _ _
  have hH₁0 : 0 ≤ gwCond₁ P κ := condEntropy_nonneg hμ _ _
  have hH₂0 : 0 ≤ gwCond₂ P κ := condEntropy_nonneg hμ _ _
  have hR₀ := nonneg_of_lt_mul_log_two hI0 h₀
  have hR₁ := nonneg_of_lt_mul_log_two hH₁0 h₁
  have hR₂ := nonneg_of_lt_mul_log_two hH₂0 h₂
  refine isAchievableGW_of_eventually hP hR₀ hR₁ hR₂ fun τ hτ => ?_
  -- The choice of `ε`.
  have hcU : 0 ≤ log (Fintype.card υ) := log_natCast_nonneg _
  obtain ⟨c, hc⟩ : ∃ c, c = 2 * log (Fintype.card υ) + gwCond₁ P κ + gwCond₂ P κ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    linarith
  obtain ⟨S, hS0, hS₀, hS₁, hS₂⟩ : ∃ S > 0, S ≤ R₀ * log 2 - gwInfo P κ ∧
      S ≤ R₁ * log 2 - gwCond₁ P κ ∧ S ≤ R₂ * log 2 - gwCond₂ P κ :=
    ⟨min (R₀ * log 2 - gwInfo P κ) (min (R₁ * log 2 - gwCond₁ P κ) (R₂ * log 2 - gwCond₂ P κ)),
      lt_min (by linarith) (lt_min (by linarith) (by linarith)), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨ε, hε0, hε1, hεc⟩ := exists_eps_mul_lt hc0 hS0
  have hU : ε * (2 * log (Fintype.card υ)) ≤ ε * c :=
    mul_le_mul_of_nonneg_left (by rw [hc]; linarith) hε0.le
  have hE₁ : ε * gwCond₁ P κ ≤ ε * c :=
    mul_le_mul_of_nonneg_left (by rw [hc]; linarith) hε0.le
  have hE₂ : ε * gwCond₂ P κ ≤ ε * c :=
    mul_le_mul_of_nonneg_left (by rw [hc]; linarith) hε0.le
  -- The bounds on the number of sequences.
  have hl₁₁ : IsPMF (gwLaw₁ P κ) := IsPMF.dist hμ _
  have hl₂₂ : IsPMF (gwLaw₂ P κ) := IsPMF.dist hμ _
  have hcard₁ : ∀ᶠ n : ℕ in atTop, ∀ v : Fin n → υ,
      (condRobustTypicalSet (gwLaw₁ P κ) ε v).card ≤ 2 ^ ⌊(n : ℝ) * R₁⌋₊ := by
    filter_upwards [eventually_exp_le_two_pow_floor (a := gwCond₁ P κ + ε * gwCond₁ P κ)
      (R := R₁) (by linarith)] with n hn v
    have h := card_condRobustTypicalSet_le hl₁₁ ε v
    rw [condEntropy_gwLaw₁ hP hκ] at h
    exact Nat.cast_le.1 (h.trans hn)
  have hcard₂ : ∀ᶠ n : ℕ in atTop, ∀ v : Fin n → υ,
      (condRobustTypicalSet (gwLaw₂ P κ) ε v).card ≤ 2 ^ ⌊(n : ℝ) * R₂⌋₊ := by
    filter_upwards [eventually_exp_le_two_pow_floor (a := gwCond₂ P κ + ε * gwCond₂ P κ)
      (R := R₂) (by linarith)] with n hn v
    have h := card_condRobustTypicalSet_le hl₂₂ ε v
    rw [condEntropy_gwLaw₂ hP hκ] at h
    exact Nat.cast_le.1 (h.trans hn)
  exact eventually_gw_code_aux (M₀ := fun n => 2 ^ ⌊(n : ℝ) * R₀⌋₊)
    (M₁ := fun n => 2 ^ ⌊(n : ℝ) * R₁⌋₊) (M₂ := fun n => 2 ^ ⌊(n : ℝ) * R₂⌋₊) hP hκ hε0 hε1 hτ
    (fun n => by positivity) (fun n => by positivity) (fun n => by positivity) hcard₁ hcard₂
    (tendsto_exp_neg_mul_of_le (b := R₀ * log 2) (K := 2) (by linarith) (by linarith) two_pos
      fun n => exp_le_two_mul_two_pow_floor n R₀)

end Achievability

end InfoTheory
