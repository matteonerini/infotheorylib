/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACAchievability
public import InfoTheoryLib.Network.MACConverse
public import InfoTheoryLib.Network.Typicality

/-!
# Slepian–Wolf coding of correlated sources

Two correlated sources `(Xᵢ, Yᵢ)`, i.i.d. with joint pmf `p(x, y)`, are encoded separately, at
rates `R₁` and `R₂`, and decoded together. The Slepian–Wolf theorem (Theorem 15.4.1) says that
the achievable rate region is `R₁ ≥ H(X | Y)`, `R₂ ≥ H(Y | X)`, `R₁ + R₂ ≥ H(X, Y)`: separate
encoding costs nothing in total rate.

The converse follows from Fano's inequality, (15.178)–(15.194). The achievability uses random
binning: each sequence `xⁿ` is thrown into one of `M₁` bins uniformly at random, and similarly for
`yⁿ`; the decoder looks for the unique jointly typical pair in the pair of bins received. A wrong
`x'ⁿ` jointly typical with `yⁿ` falls in the right bin with probability `1/M₁`, and there are at
most `e^{n(H(X|Y)+2ε)}` such `x'ⁿ` (Theorem 15.2.2), (15.167)–(15.177).

## Main definitions

* `SWCode M₁ M₂ n α β`: **(15.154)–(15.156)** a distributed source code with `M₁` and `M₂`
  indices.
* `SWCode.errProb`: **(15.157)** its probability of error.
* `IsAchievableSW q R₁ R₂`, `swAchievableRegion q`: achievable rate pairs and the achievable rate
  region, the closure of the achievable rate pairs.
* `swRegion q`: **(15.158)–(15.160)** the Slepian–Wolf region.

## Main statements

* `SWCode.mul_condEntropy_fst_le`, `SWCode.mul_condEntropy_snd_le`, `SWCode.mul_entropy_le`:
  (15.178)–(15.194) for a single code.
* `IsAchievableSW.mem_swRegion`: **Theorem 15.4.1 (converse).**
* `sum_bins_errProb_le`: (15.171)–(15.177), the probability of error of random binning.
* `isAchievableSW_of_lt`: **Theorem 15.4.1 (achievability).**
* `swAchievableRegion_eq`: **Theorem 15.4.1 (Slepian–Wolf).**

## Implementation notes

As for the rate distortion codes of Chapter 10, a code of rate `R` has `⌊e^{nR}⌋` indices, the
largest number allowed by the rate, and rates are in nats. The random bin assignments are
functions on `Fin N`, where `N` is the number of source sequences, so that the averaging lemmas
for random codebooks (`sum_codebook_eval₂₁`, …) apply.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 15.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Definition (15.154)–(15.156).** A `((M₁, M₂), n)` distributed source code: an encoder for
each source and a decoder reconstructing both sequences from the two indices. -/
structure SWCode (M₁ M₂ n : ℕ) (α β : Type*) where
  /-- The encoder `f₁ : 𝒳ⁿ → {0, …, M₁ - 1}`. -/
  enc₁ : (Fin n → α) → Fin M₁
  /-- The encoder `f₂ : 𝒴ⁿ → {0, …, M₂ - 1}`. -/
  enc₂ : (Fin n → β) → Fin M₂
  /-- The decoder `g : {0, …, M₁ - 1} × {0, …, M₂ - 1} → 𝒳ⁿ × 𝒴ⁿ`. -/
  dec : Fin M₁ × Fin M₂ → (Fin n → α) × (Fin n → β)

namespace SWCode

variable {M₁ M₂ n : ℕ} (q : α × β → ℝ) (c : SWCode M₁ M₂ n α β)

/-- The pair of indices `(f₁(xⁿ), f₂(yⁿ))`. -/
def index (z : (Fin n → α) × (Fin n → β)) : Fin M₁ × Fin M₂ := (c.enc₁ z.1, c.enc₂ z.2)

open Classical in
/-- **Definition (15.157).** The probability of error `Pr{g(f₁(Xⁿ), f₂(Yⁿ)) ≠ (Xⁿ, Yⁿ)}`. -/
def errProb : ℝ := ∑ z, if c.dec (c.index z) ≠ z then jointIid q n z else 0

lemma errProb_eq : c.errProb q = InfoTheory.errProb (jointIid q n) id c.index c.dec := by
  classical
  unfold errProb InfoTheory.errProb
  exact sum_congr rfl fun z _ => by by_cases h : c.dec (c.index z) = z <;> simp [h]

variable {q}

lemma errProb_nonneg (hq : IsPMF q) : 0 ≤ c.errProb q := by
  classical
  exact sum_nonneg fun z _ => by split_ifs <;> simp [jointIid_nonneg hq.nonneg]

end SWCode

/-- **Definition (Section 15.4).** A rate pair `(R₁, R₂)` (in nats) is achievable if there are
`((⌊e^{nR₁}⌋, ⌊e^{nR₂}⌋), n)` distributed source codes with probability of error tending to `0`. -/
def IsAchievableSW (q : α × β → ℝ) (R₁ R₂ : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, SWCode ⌊exp (n * R₁)⌋₊ ⌊exp (n * R₂)⌋₊ n α β,
    Tendsto (fun n => (c n).errProb q) atTop (𝓝 0)

/-- **Definition (Section 15.4).** The achievable rate region is the closure of the set of
achievable rate pairs. -/
def swAchievableRegion (q : α × β → ℝ) : Set (ℝ × ℝ) := closure {R | IsAchievableSW q R.1 R.2}

/-- **(15.158)–(15.160)** The Slepian–Wolf region `R₁ ≥ H(X | Y)`, `R₂ ≥ H(Y | X)`,
`R₁ + R₂ ≥ H(X, Y)`. -/
def swRegion (q : α × β → ℝ) : Set (ℝ × ℝ) :=
  {R | H[Prod.fst | Prod.snd ; q] ≤ R.1 ∧ H[Prod.snd | Prod.fst ; q] ≤ R.2 ∧ entropy q ≤ R.1 + R.2}

lemma isClosed_swRegion (q : α × β → ℝ) : IsClosed (swRegion q) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_const (continuous_fst.add continuous_snd)))

/-! ### The converse -/

namespace SWCode

variable {q : α × β → ℝ} {M₁ M₂ n : ℕ} (c : SWCode M₁ M₂ n α β)

lemma log_card_seq (hq : IsPMF q) (n : ℕ) :
    log (Fintype.card ((Fin n → α) × (Fin n → β))) =
      n * log (Fintype.card α * Fintype.card β) := by
  have hα : 0 < Fintype.card α := Fintype.card_pos_iff.2 ⟨(Classical.choice
    (Fintype.card_pos_iff.1 (card_pos_of_isPMF hq))).1⟩
  have hβ : 0 < Fintype.card β := Fintype.card_pos_iff.2 ⟨(Classical.choice
    (Fintype.card_pos_iff.1 (card_pos_of_isPMF hq))).2⟩
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [log_mul (by positivity) (by positivity), log_pow, log_pow,
    log_mul (by positivity) (by positivity)]
  ring

/-- **(15.178)** Fano's inequality: `H(Xⁿ, Yⁿ | I₀, J₀) ≤ log 2 + Pₑ^(n) n log (|𝒳| |𝒴|)`. -/
lemma condEntropy_seq_le (hq : IsPMF q) :
    H[id | c.index ; jointIid q n] ≤
      log 2 + c.errProb q * (n * log (Fintype.card α * Fintype.card β)) := by
  have h := fano_weak (jointIid_isPMF hq n) id c.index c.dec
  rwa [← c.errProb_eq, log_card_seq hq] at h

/-- **(15.187)–(15.193)** `n H(X | Y) ≤ log M₁ + log 2 + Pₑ^(n) n log (|𝒳| |𝒴|)`. -/
theorem mul_condEntropy_fst_le (hq : IsPMF q) :
    n * H[Prod.fst | Prod.snd ; q] ≤
      log M₁ + log 2 + c.errProb q * (n * log (Fintype.card α * Fintype.card β)) := by
  set μ := jointIid q n
  have hμ : IsPMF μ := jointIid_isPMF hq n
  set I₀ : (Fin n → α) × (Fin n → β) → Fin M₁ := fun z => c.enc₁ z.1
  -- `H(Xⁿ | Yⁿ) ≤ H(I₀, Xⁿ | Yⁿ) = H(I₀ | Yⁿ) + H(Xⁿ | I₀, Yⁿ)`.
  have h1 : H[Prod.fst | Prod.snd ; μ] ≤ H[pair I₀ Prod.fst | Prod.snd ; μ] := by
    have e : H[pair I₀ Prod.fst | Prod.snd ; μ] = H[pair Prod.fst I₀ | Prod.snd ; μ] :=
      condEntropy_congr_left hμ _ Prod.swap Prod.swap_injective fun _ => rfl
    rw [e, chain_rule_cond hμ]
    linarith [condEntropy_nonneg hμ I₀ (pair (Prod.fst : (Fin n → α) × (Fin n → β) → _)
      Prod.snd)]
  have h2 := chain_rule_cond hμ I₀ Prod.fst Prod.snd
  have h3 : H[I₀ | Prod.snd ; μ] ≤ log M₁ := by
    have := (condEntropy_le_entropy hμ I₀ Prod.snd).trans (entropyRV_le_log_card hμ I₀)
    rwa [Fintype.card_fin] at this
  -- `H(Xⁿ | I₀, Yⁿ) ≤ H(Xⁿ, Yⁿ | I₀, J₀)`.
  have h4 : H[Prod.fst | pair I₀ Prod.snd ; μ] ≤ H[id | c.index ; μ] := by
    have := condEntropy_comp_le hμ id (pair I₀ Prod.snd) Prod.fst
    refine this.trans ?_
    exact condEntropy_le_condEntropy_comp hμ id (pair I₀ Prod.snd)
      (fun w : Fin M₁ × (Fin n → β) => (w.1, c.enc₂ w.2))
  have h5 := c.condEntropy_seq_le hq
  rw [condEntropy_jointIid_fst hq] at h1
  linarith

/-- **(15.194)** `n H(Y | X) ≤ log M₂ + log 2 + Pₑ^(n) n log (|𝒳| |𝒴|)`. -/
theorem mul_condEntropy_snd_le (hq : IsPMF q) :
    n * H[Prod.snd | Prod.fst ; q] ≤
      log M₂ + log 2 + c.errProb q * (n * log (Fintype.card α * Fintype.card β)) := by
  set μ := jointIid q n
  have hμ : IsPMF μ := jointIid_isPMF hq n
  set J₀ : (Fin n → α) × (Fin n → β) → Fin M₂ := fun z => c.enc₂ z.2
  have h1 : H[Prod.snd | Prod.fst ; μ] ≤ H[pair J₀ Prod.snd | Prod.fst ; μ] := by
    have e : H[pair J₀ Prod.snd | Prod.fst ; μ] = H[pair Prod.snd J₀ | Prod.fst ; μ] :=
      condEntropy_congr_left hμ _ Prod.swap Prod.swap_injective fun _ => rfl
    rw [e, chain_rule_cond hμ]
    linarith [condEntropy_nonneg hμ J₀ (pair (Prod.snd : (Fin n → α) × (Fin n → β) → _)
      Prod.fst)]
  have h2 := chain_rule_cond hμ J₀ Prod.snd Prod.fst
  have h3 : H[J₀ | Prod.fst ; μ] ≤ log M₂ := by
    have := (condEntropy_le_entropy hμ J₀ Prod.fst).trans (entropyRV_le_log_card hμ J₀)
    rwa [Fintype.card_fin] at this
  have h4 : H[Prod.snd | pair J₀ Prod.fst ; μ] ≤ H[id | c.index ; μ] := by
    have := condEntropy_comp_le hμ id (pair J₀ Prod.fst) Prod.snd
    refine this.trans ?_
    exact condEntropy_le_condEntropy_comp hμ id (pair J₀ Prod.fst)
      (fun w : Fin M₂ × (Fin n → α) => (c.enc₁ w.2, w.1))
  have h5 := c.condEntropy_seq_le hq
  rw [condEntropy_jointIid_snd hq] at h1
  linarith

/-- **(15.181)–(15.186)** `n H(X, Y) ≤ log (M₁ M₂) + log 2 + Pₑ^(n) n log (|𝒳| |𝒴|)`. -/
theorem mul_entropy_le (hq : IsPMF q) :
    n * entropy q ≤
      log (M₁ * M₂) + log 2 + c.errProb q * (n * log (Fintype.card α * Fintype.card β)) := by
  set μ := jointIid q n
  have hμ : IsPMF μ := jointIid_isPMF hq n
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ id c.index
  have h2 := mutualInfo_eq_entropy_sub_condEntropy' hμ id c.index
  have h3 := condEntropy_nonneg hμ c.index id
  have h4 : H[c.index ; μ] ≤ log (M₁ * M₂) := by
    have := entropyRV_le_log_card hμ c.index
    rwa [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul] at this
  have h5 : H[id ; μ] = n * entropy q := by
    rw [entropyRV, dist_id, entropy_jointIid hq]
  have h6 := c.condEntropy_seq_le hq
  linarith

end SWCode

lemma log_floor_exp_le {x : ℝ} {M : ℕ} (hM : M = ⌊exp x⌋₊) (h : 0 < M) : log M ≤ x := by
  have h1 : (M : ℝ) ≤ exp x := by rw [hM]; exact Nat.floor_le (exp_pos x).le
  have h0 : (0 : ℝ) < M := by exact_mod_cast h
  calc log M ≤ log (exp x) := log_le_log h0 h1
    _ = x := log_exp x

/-- The limit argument of the converse: if `n a ≤ n R + log 2 + Pₙ n L` for all `n ≥ 1` and
`Pₙ → 0`, then `a ≤ R`. -/
lemma le_of_sw_bound {a R L : ℝ} {P : ℕ → ℝ} (hP : Tendsto P atTop (𝓝 0))
    (h : ∀ n : ℕ, 0 < n → n * a ≤ n * R + log 2 + P n * (n * L)) : a ≤ R := by
  have hlim : Tendsto (fun n : ℕ => R + log 2 / n + P n * L) atTop (𝓝 (R + 0 + 0 * L)) :=
    ((tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (log 2))).add
      (hP.mul_const L))
  rw [add_zero, zero_mul, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : (n : ℝ) * (R + log 2 / n + P n * L) = n * R + log 2 + P n * (n * L) := by
    field_simp
  exact le_of_mul_le_mul_left (by rw [e]; exact h n hn) hn'

/-- **Theorem 15.4.1 (Slepian–Wolf, converse), (15.178)–(15.194).** Every achievable rate pair
satisfies `R₁ ≥ H(X | Y)`, `R₂ ≥ H(Y | X)` and `R₁ + R₂ ≥ H(X, Y)`. -/
theorem IsAchievableSW.mem_swRegion {q : α × β → ℝ} (hq : IsPMF q) {R₁ R₂ : ℝ}
    (h : IsAchievableSW q R₁ R₂) : (R₁, R₂) ∈ swRegion q := by
  obtain ⟨c, hc⟩ := h
  have hne : Nonempty (α × β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  obtain ⟨a, b⟩ := Classical.choice hne
  set L := log (Fintype.card α * Fintype.card β)
  have hM₁ : ∀ n : ℕ, 0 < ⌊exp (n * R₁)⌋₊ := fun n =>
    Fin.pos ((c n).enc₁ fun _ => a)
  have hM₂ : ∀ n : ℕ, 0 < ⌊exp (n * R₂)⌋₊ := fun n =>
    Fin.pos ((c n).enc₂ fun _ => b)
  have hl₁ : ∀ n : ℕ, log ⌊exp (n * R₁)⌋₊ ≤ n * R₁ := fun n => log_floor_exp_le rfl (hM₁ n)
  have hl₂ : ∀ n : ℕ, log ⌊exp (n * R₂)⌋₊ ≤ n * R₂ := fun n => log_floor_exp_le rfl (hM₂ n)
  refine ⟨le_of_sw_bound (L := L) hc fun n _ => ?_, le_of_sw_bound (L := L) hc fun n _ => ?_,
    le_of_sw_bound (L := L) hc fun n _ => ?_⟩
  · linarith [(c n).mul_condEntropy_fst_le hq, hl₁ n]
  · linarith [(c n).mul_condEntropy_snd_le hq, hl₂ n]
  · have h := (c n).mul_entropy_le hq
    rw [log_mul (by exact_mod_cast (hM₁ n).ne') (by exact_mod_cast (hM₂ n).ne')] at h
    have e : (n : ℝ) * (R₁ + R₂) = n * R₁ + n * R₂ := by ring
    rw [e]
    linarith [hl₁ n, hl₂ n]

/-! ### Random binning -/

section Binning

variable {M₁ M₂ n : ℕ}

open Classical in
/-- **Section 15.4.1** Decoding of random binning: given the indices `w`, declare the unique
jointly typical pair in the pair of bins `w`, and `d` if there is none or more than one. -/
def swTypicalDecode (A : Finset ((Fin n → α) × (Fin n → β))) (f₁ : (Fin n → α) → Fin M₁)
    (f₂ : (Fin n → β) → Fin M₂) (d : (Fin n → α) × (Fin n → β)) (w : Fin M₁ × Fin M₂) :
    (Fin n → α) × (Fin n → β) :=
  if h : ∃ z ∈ A, (f₁ z.1, f₂ z.2) = w ∧ ∀ z' ∈ A, (f₁ z'.1, f₂ z'.2) = w → z' = z then
    h.choose else d

/-- The distributed source code with the bin assignments `f₁`, `f₂` and typical decoding. -/
def swTypicalCode (A : Finset ((Fin n → α) × (Fin n → β))) (f₁ : (Fin n → α) → Fin M₁)
    (f₂ : (Fin n → β) → Fin M₂) (d : (Fin n → α) × (Fin n → β)) : SWCode M₁ M₂ n α β :=
  ⟨f₁, f₂, swTypicalDecode A f₁ f₂ d⟩

lemma swTypicalDecode_eq {A : Finset ((Fin n → α) × (Fin n → β))} {f₁ : (Fin n → α) → Fin M₁}
    {f₂ : (Fin n → β) → Fin M₂} (d : (Fin n → α) × (Fin n → β)) {z : (Fin n → α) × (Fin n → β)}
    (hz : z ∈ A) (huniq : ∀ z' ∈ A, (f₁ z'.1, f₂ z'.2) = (f₁ z.1, f₂ z.2) → z' = z) :
    swTypicalDecode A f₁ f₂ d (f₁ z.1, f₂ z.2) = z := by
  have h : ∃ z₀ ∈ A, (f₁ z₀.1, f₂ z₀.2) = (f₁ z.1, f₂ z.2) ∧
      ∀ z' ∈ A, (f₁ z'.1, f₂ z'.2) = (f₁ z.1, f₂ z.2) → z' = z₀ := ⟨z, hz, rfl, huniq⟩
  unfold swTypicalDecode
  split
  · next h' => exact huniq _ h'.choose_spec.1 h'.choose_spec.2.1
  · next h' => exact absurd h h'

open Classical in
/-- **(15.167)–(15.172)** A decoding error occurs only if `(xⁿ, yⁿ)` is not typical, or another
typical pair is in the same pair of bins: with the first, the second or both sequences
different. -/
lemma swTypicalDecode_ne_le (A : Finset ((Fin n → α) × (Fin n → β)))
    (f₁ : (Fin n → α) → Fin M₁) (f₂ : (Fin n → β) → Fin M₂) (d : (Fin n → α) × (Fin n → β))
    (x : Fin n → α) (y : Fin n → β) :
    (if swTypicalDecode A f₁ f₂ d (f₁ x, f₂ y) ≠ (x, y) then (1 : ℝ) else 0) ≤
      (if (x, y) ∈ A then 0 else 1) +
        ∑ x' ∈ univ.erase x, (if (x', y) ∈ A then 1 else 0) * (if f₁ x' = f₁ x then 1 else 0) +
        ∑ y' ∈ univ.erase y, (if (x, y') ∈ A then 1 else 0) * (if f₂ y' = f₂ y then 1 else 0) +
        ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y, (if (x', y') ∈ A then 1 else 0) *
          ((if f₁ x' = f₁ x then 1 else 0) * (if f₂ y' = f₂ y then 1 else 0)) := by
  have hind : ∀ P Q : Prop, [Decidable P] → [Decidable Q] →
      0 ≤ (if P then (1 : ℝ) else 0) * (if Q then 1 else 0) := fun P Q _ _ => by
    split_ifs <;> norm_num
  have hS₁ := sum_nonneg fun x' (_ : x' ∈ univ.erase x) =>
    hind ((x', y) ∈ A) (f₁ x' = f₁ x)
  have hS₂ := sum_nonneg fun y' (_ : y' ∈ univ.erase y) =>
    hind ((x, y') ∈ A) (f₂ y' = f₂ y)
  have hind₃ : ∀ x' y', 0 ≤ (if (x', y') ∈ A then (1 : ℝ) else 0) *
      ((if f₁ x' = f₁ x then 1 else 0) * (if f₂ y' = f₂ y then 1 else 0)) := fun x' y' =>
    mul_nonneg (by split_ifs <;> norm_num) (hind _ _)
  have hS₃ := sum_nonneg fun x' (_ : x' ∈ univ.erase x) =>
    sum_nonneg fun y' (_ : y' ∈ univ.erase y) => hind₃ x' y'
  have h0 : 0 ≤ (if (x, y) ∈ A then (0 : ℝ) else 1) := by split_ifs <;> norm_num
  by_cases hd : swTypicalDecode A f₁ f₂ d (f₁ x, f₂ y) = (x, y)
  · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte]
    linarith
  simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases hz : (x, y) ∈ A
  swap
  · simp only [hz, ↓reduceIte]
    linarith
  obtain ⟨⟨x', y'⟩, hz', heq, hne⟩ : ∃ z' ∈ A, (f₁ z'.1, f₂ z'.2) = (f₁ x, f₂ y) ∧
      z' ≠ (x, y) := by
    by_contra hne
    push Not at hne
    exact hd (swTypicalDecode_eq (z := (x, y)) d hz fun z' h1 h2 => hne z' h1 h2)
  simp only [Prod.mk.injEq] at heq
  simp only [hz, ↓reduceIte, zero_add]
  by_cases hx : x' = x
  · subst hx
    have hy : y' ≠ y := fun h => hne (by rw [h])
    have := single_le_sum (f := fun y' => (if (x', y') ∈ A then (1 : ℝ) else 0) *
      (if f₂ y' = f₂ y then 1 else 0)) (fun y' _ => hind _ _) (mem_erase.2 ⟨hy, mem_univ y'⟩)
    simp only [hz', heq.2, ↓reduceIte, mul_one] at this
    linarith
  by_cases hy : y' = y
  · subst hy
    have := single_le_sum (f := fun x' => (if (x', y') ∈ A then (1 : ℝ) else 0) *
      (if f₁ x' = f₁ x then 1 else 0)) (fun x' _ => hind _ _) (mem_erase.2 ⟨hx, mem_univ x'⟩)
    simp only [hz', heq.1, ↓reduceIte, mul_one] at this
    linarith
  have h1 := single_le_sum (f := fun y' => (if (x', y') ∈ A then (1 : ℝ) else 0) *
      ((if f₁ x' = f₁ x then 1 else 0) * (if f₂ y' = f₂ y then 1 else 0)))
    (fun y' _ => hind₃ x' y') (mem_erase.2 ⟨hy, mem_univ y'⟩)
  have h2 := single_le_sum (f := fun x' => ∑ y' ∈ univ.erase y,
      (if (x', y') ∈ A then (1 : ℝ) else 0) *
        ((if f₁ x' = f₁ x then 1 else 0) * (if f₂ y' = f₂ y then 1 else 0)))
    (fun x' _ => sum_nonneg fun y' _ => hind₃ x' y') (mem_erase.2 ⟨hx, mem_univ x'⟩)
  have hv : (if (x', y') ∈ A then (1 : ℝ) else 0) *
      ((if f₁ x' = f₁ x then 1 else 0) * (if f₂ y' = f₂ y then 1 else 0)) = 1 := by
    simp [hz', heq.1, heq.2]
  rw [hv] at h1
  linarith

/-- The probability that two distinct sequences fall in the same random bin is `1/M`. -/
lemma sum_bins_eq_eq {N M : ℕ} (hM : 0 < M) {i i' : Fin N} (h : i ≠ i') :
    ∑ B : Fin N → Fin M, iidPMF (uniformPMF (Fin M)) N B *
      (if B i' = B i then (1 : ℝ) else 0) = 1 / M := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have h₂ := sum_iidPMF_eval₂ (uniformPMF_isPMF (α := Fin M)) h
    (fun b b' => if b' = b then (1 : ℝ) else 0)
  rw [h₂]
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have e : ∀ x : Fin M, ∑ x', uniformPMF (Fin M) x * uniformPMF (Fin M) x' *
      (if x' = x then (1 : ℝ) else 0) = 1 / M ^ 2 := fun x => by
    rw [sum_eq_single x (fun b _ hb => by simp [hb]) (by simp)]
    simp only [uniformPMF, Fintype.card_fin, ↓reduceIte, mul_one]
    ring
  simp only [e, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Binning

/-! ### The random binning bound -/

section RandomBins

variable {M₁ M₂ : ℕ} (n : ℕ)

/-- The number of sequences of length `n`. -/
abbrev seqCard (γ : Type*) [Fintype γ] (n : ℕ) : ℕ := Fintype.card (Fin n → γ)

variable (α β M₁ M₂) in
/-- The law of the random bin assignments: every sequence is put in a uniformly chosen bin,
independently. -/
def binLaw : (Fin (seqCard α n) → Fin M₁) × (Fin (seqCard β n) → Fin M₂) → ℝ :=
  prodDist (iidPMF (uniformPMF (Fin M₁)) _) (iidPMF (uniformPMF (Fin M₂)) _)

/-- The code with the bin assignments `B` and typical decoding. -/
def binCode (A : Finset ((Fin n → α) × (Fin n → β)))
    (B : (Fin (seqCard α n) → Fin M₁) × (Fin (seqCard β n) → Fin M₂))
    (d : (Fin n → α) × (Fin n → β)) : SWCode M₁ M₂ n α β :=
  swTypicalCode A (fun x => B.1 (Fintype.equivFin _ x)) (fun y => B.2 (Fintype.equivFin _ y)) d

omit [Fintype α] [Fintype β] in
lemma sum_mul_sum_comm' {ι κ : Type*} [Fintype ι] (s : Finset κ) (μ : ι → ℝ)
    (g : κ → ι → ℝ) : ∑ B, μ B * ∑ k ∈ s, g k B = ∑ k ∈ s, ∑ B, μ B * g k B := by
  simp only [mul_sum]
  exact sum_comm

omit [Fintype α] [Fintype β] in
lemma sum_mul_sum_mul_comm {ι κ : Type*} [Fintype ι] (s : Finset κ) (μ : ι → ℝ) (a : κ → ℝ)
    (g : κ → ι → ℝ) : ∑ B, μ B * ∑ k ∈ s, a k * g k B = ∑ k ∈ s, a k * ∑ B, μ B * g k B := by
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun k _ => sum_congr rfl fun B _ => by ring

variable {n}

lemma binLaw_isPMF (h₁ : 0 < M₁) (h₂ : 0 < M₂) : IsPMF (binLaw α β M₁ M₂ n) := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  exact (iidPMF_isPMF uniformPMF_isPMF _).prodDist (iidPMF_isPMF uniformPMF_isPMF _)

lemma sum_binLaw_fst (h₂ : 0 < M₂) (g : (Fin (seqCard α n) → Fin M₁) → ℝ) :
    ∑ B, binLaw α β M₁ M₂ n B * g B.1 = ∑ B₁, iidPMF (uniformPMF (Fin M₁)) _ B₁ * g B₁ := by
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun B₁ _ => ?_
  simp only [binLaw, prodDist, mul_comm (iidPMF (uniformPMF (Fin M₁)) _ B₁), mul_assoc,
    ← sum_mul]
  rw [(iidPMF_isPMF uniformPMF_isPMF _).sum_eq_one, one_mul]

lemma sum_binLaw_snd (h₁ : 0 < M₁) (g : (Fin (seqCard β n) → Fin M₂) → ℝ) :
    ∑ B, binLaw α β M₁ M₂ n B * g B.2 = ∑ B₂, iidPMF (uniformPMF (Fin M₂)) _ B₂ * g B₂ := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun B₂ _ => ?_
  simp only [binLaw, prodDist, mul_assoc, ← sum_mul]
  rw [(iidPMF_isPMF uniformPMF_isPMF _).sum_eq_one, one_mul]

lemma sum_binLaw_mul (g : (Fin (seqCard α n) → Fin M₁) → ℝ)
    (h : (Fin (seqCard β n) → Fin M₂) → ℝ) :
    ∑ B, binLaw α β M₁ M₂ n B * (g B.1 * h B.2) =
      (∑ B₁, iidPMF (uniformPMF (Fin M₁)) _ B₁ * g B₁) *
        ∑ B₂, iidPMF (uniformPMF (Fin M₂)) _ B₂ * h B₂ := by
  rw [Fintype.sum_prod_type, sum_mul_sum]
  exact sum_congr rfl fun B₁ _ => sum_congr rfl fun B₂ _ => by simp only [binLaw, prodDist]; ring

open Classical in
/-- **(15.171)–(15.177)** Averaged over the random bin assignments, the probability of error of
typical decoding is at most `Pr{(Xⁿ, Yⁿ) ∉ A_ε^(n)} + e^{n(H(X|Y)+2ε)}/M₁ + e^{n(H(Y|X)+2ε)}/M₂ +
e^{n(H(X,Y)+ε)}/(M₁ M₂)`. -/
theorem sum_bins_errProb_le {q : α × β → ℝ} (hq : IsPMF q) (h₁ : 0 < M₁) (h₂ : 0 < M₂) (ε : ℝ)
    (d : (Fin n → α) × (Fin n → β)) :
    ∑ B, binLaw α β M₁ M₂ n B * (binCode n (jointTypicalSet q n ε) B d).errProb q ≤
      (1 - prob (jointIid q n) (jointTypicalSet q n ε)) +
        exp (n * (H[Prod.fst | Prod.snd ; q] + 2 * ε)) / M₁ +
        exp (n * (H[Prod.snd | Prod.fst ; q] + 2 * ε)) / M₂ +
        exp (n * (entropy q + ε)) / (M₁ * M₂) := by
  set A := jointTypicalSet q n ε
  set μ := binLaw α β M₁ M₂ n
  have hμ := binLaw_isPMF (α := α) (β := β) (n := n) h₁ h₂
  set p := jointIid q n
  have hp := jointIid_isPMF hq n
  set e₁ := Fintype.equivFin (Fin n → α)
  set e₂ := Fintype.equivFin (Fin n → β)
  set K₁ := exp (n * (H[Prod.fst | Prod.snd ; q] + 2 * ε))
  set K₂ := exp (n * (H[Prod.snd | Prod.fst ; q] + 2 * ε))
  set K₃ := exp (n * (entropy q + ε))
  have hM₁ : (0 : ℝ) < M₁ := by exact_mod_cast h₁
  have hM₂ : (0 : ℝ) < M₂ := by exact_mod_cast h₂
  -- The error indicator.
  set E : (Fin (seqCard α n) → Fin M₁) × (Fin (seqCard β n) → Fin M₂) →
      (Fin n → α) × (Fin n → β) → ℝ := fun B z =>
    if (binCode n A B d).dec ((binCode n A B d).index z) ≠ z then 1 else 0
  have herr : ∀ B, (binCode n A B d).errProb q = ∑ z, p z * E B z := fun B => by
    simp only [SWCode.errProb, E]
    exact sum_congr rfl fun z _ => by split_ifs <;> simp [p]
  -- For a fixed pair `z = (x, y)`, average over the bins.
  have hz : ∀ x y, ∑ B, μ B * E B (x, y) ≤
      (if (x, y) ∈ A then 0 else 1) + K₁ / M₁ + K₂ / M₂ + K₃ / (M₁ * M₂) := by
    intro x y
    set a : (Fin n → α) → ℝ := fun x' => if (x', y) ∈ A then 1 else 0
    set b : (Fin n → β) → ℝ := fun y' => if (x, y') ∈ A then 1 else 0
    set c : (Fin n → α) → (Fin n → β) → ℝ := fun x' y' => if (x', y') ∈ A then 1 else 0
    set g₁ : (Fin n → α) → (Fin (seqCard α n) → Fin M₁) × (Fin (seqCard β n) → Fin M₂) → ℝ :=
      fun x' B => if B.1 (e₁ x') = B.1 (e₁ x) then 1 else 0
    set g₂ : (Fin n → β) → (Fin (seqCard α n) → Fin M₁) × (Fin (seqCard β n) → Fin M₂) → ℝ :=
      fun y' B => if B.2 (e₂ y') = B.2 (e₂ y) then 1 else 0
    have hpt : ∀ B, E B (x, y) ≤ (if (x, y) ∈ A then 0 else 1) +
        ∑ x' ∈ univ.erase x, a x' * g₁ x' B + ∑ y' ∈ univ.erase y, b y' * g₂ y' B +
        ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y, c x' y' * (g₁ x' B * g₂ y' B) := fun B =>
      swTypicalDecode_ne_le A (fun x => B.1 (e₁ x)) (fun y => B.2 (e₂ y)) d x y
    have hg₁ : ∀ x' ∈ univ.erase x, ∑ B, μ B * g₁ x' B = 1 / M₁ := fun x' hx' => by
      exact (sum_binLaw_fst h₂ (fun B₁ => if B₁ (e₁ x') = B₁ (e₁ x) then 1 else 0)).trans
        (sum_bins_eq_eq h₁ (e₁.injective.ne (ne_of_mem_erase hx')).symm)
    have hg₂ : ∀ y' ∈ univ.erase y, ∑ B, μ B * g₂ y' B = 1 / M₂ := fun y' hy' => by
      exact (sum_binLaw_snd h₁ (fun B₂ => if B₂ (e₂ y') = B₂ (e₂ y) then 1 else 0)).trans
        (sum_bins_eq_eq h₂ (e₂.injective.ne (ne_of_mem_erase hy')).symm)
    have hg₁₂ : ∀ x' ∈ univ.erase x, ∀ y' ∈ univ.erase y,
        ∑ B, μ B * (g₁ x' B * g₂ y' B) = 1 / M₁ * (1 / M₂) := fun x' hx' y' hy' => by
      refine (sum_binLaw_mul (fun B₁ => if B₁ (e₁ x') = B₁ (e₁ x) then 1 else 0)
        (fun B₂ => if B₂ (e₂ y') = B₂ (e₂ y) then 1 else 0)).trans ?_
      rw [sum_bins_eq_eq h₁ (e₁.injective.ne (ne_of_mem_erase hx')).symm,
        sum_bins_eq_eq h₂ (e₂.injective.ne (ne_of_mem_erase hy')).symm]
    -- The fibers and the typical set are small, Theorem 15.2.2 and Theorem 15.2.1.
    have ha : ∑ x' ∈ univ.erase x, a x' ≤ K₁ := by
      refine le_trans ?_ (card_fiber_jointTypicalSet_le hq n ε y)
      rw [natCast_card_filter]
      exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by
        simp only [a]; split_ifs <;> norm_num
    have hb : ∑ y' ∈ univ.erase y, b y' ≤ K₂ := by
      refine le_trans ?_ (card_fiber_jointTypicalSet_le' hq n ε x)
      rw [natCast_card_filter]
      exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => by
        simp only [b]; split_ifs <;> norm_num
    have hc : ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y, c x' y' ≤ K₃ := by
      refine le_trans ?_ (card_jointTypicalSet_le hq n ε)
      have : ((#A : ℕ) : ℝ) = ∑ x', ∑ y', c x' y' := by
        rw [← Fintype.sum_prod_type']
        change _ = ∑ z, if z ∈ A then (1 : ℝ) else 0
        rw [sum_boole, filter_mem_eq_inter, univ_inter]
      have hc0 : ∀ x' y', 0 ≤ c x' y' := fun x' y' => by simp only [c]; split_ifs <;> norm_num
      rw [this]
      calc ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y, c x' y'
          ≤ ∑ x' ∈ univ.erase x, ∑ y', c x' y' := sum_le_sum fun x' _ =>
            sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun y' _ _ => hc0 x' y'
        _ ≤ ∑ x', ∑ y', c x' y' := sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
            fun x' _ _ => sum_nonneg fun y' _ => hc0 x' y'
    calc ∑ B, μ B * E B (x, y)
        ≤ ∑ B, μ B * ((if (x, y) ∈ A then 0 else 1) +
            ∑ x' ∈ univ.erase x, a x' * g₁ x' B + ∑ y' ∈ univ.erase y, b y' * g₂ y' B +
            ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y, c x' y' * (g₁ x' B * g₂ y' B)) :=
          sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (hpt B) (hμ.nonneg B)
      _ = (if (x, y) ∈ A then 0 else 1) + ∑ x' ∈ univ.erase x, a x' * (1 / M₁) +
            ∑ y' ∈ univ.erase y, b y' * (1 / M₂) +
            ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y, c x' y' * (1 / M₁ * (1 / M₂)) := by
          have e0 : ∑ B, μ B * (if (x, y) ∈ A then (0 : ℝ) else 1) =
              if (x, y) ∈ A then 0 else 1 := by
            rw [← sum_mul, hμ.sum_eq_one, one_mul]
          have e1 : ∑ B, μ B * ∑ x' ∈ univ.erase x, a x' * g₁ x' B =
              ∑ x' ∈ univ.erase x, a x' * (1 / M₁) := by
            rw [sum_mul_sum_mul_comm]
            exact sum_congr rfl fun x' hx' => by rw [hg₁ x' hx']
          have e2 : ∑ B, μ B * ∑ y' ∈ univ.erase y, b y' * g₂ y' B =
              ∑ y' ∈ univ.erase y, b y' * (1 / M₂) := by
            rw [sum_mul_sum_mul_comm]
            exact sum_congr rfl fun y' hy' => by rw [hg₂ y' hy']
          have e3 : ∑ B, μ B * ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y,
              c x' y' * (g₁ x' B * g₂ y' B) =
              ∑ x' ∈ univ.erase x, ∑ y' ∈ univ.erase y, c x' y' * (1 / M₁ * (1 / M₂)) := by
            rw [sum_mul_sum_comm']
            refine sum_congr rfl fun x' hx' => ?_
            rw [sum_mul_sum_mul_comm]
            exact sum_congr rfl fun y' hy' => by rw [hg₁₂ x' hx' y' hy']
          simp only [mul_add, sum_add_distrib]
          rw [e0, e1, e2, e3]
      _ ≤ _ := by
          simp only [← sum_mul]
          have e3 : K₃ / (M₁ * M₂) = K₃ * (1 / M₁ * (1 / M₂)) := by field_simp
          rw [div_eq_mul_one_div K₁, div_eq_mul_one_div K₂, e3]
          gcongr
  calc ∑ B, μ B * (binCode n A B d).errProb q
      = ∑ z, p z * ∑ B, μ B * E B z := by
        simp only [herr, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun z _ => sum_congr rfl fun B _ => by ring
    _ ≤ ∑ z, p z * ((if z ∈ A then 0 else 1) + K₁ / M₁ + K₂ / M₂ + K₃ / (M₁ * M₂)) :=
        sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hz z.1 z.2) (hp.nonneg z)
    _ = _ := by
        simp only [mul_add, sum_add_distrib, ← sum_mul]
        rw [sum_mul_ite_not_mem hp, show ∑ i, p i = 1 from hp.sum_eq_one]
        ring

end RandomBins

/-! ### Theorem 15.4.1 -/

lemma half_exp_le_floor_exp {x : ℝ} (hx : 0 ≤ x) : exp x / 2 ≤ ⌊exp x⌋₊ := by
  have h1 : (1 : ℝ) ≤ ⌊exp x⌋₊ := by
    have : 1 ≤ ⌊exp x⌋₊ := Nat.le_floor (by simpa using one_le_exp hx)
    exact_mod_cast this
  have h2 := Nat.lt_floor_add_one (exp x)
  linarith

lemma div_floor_exp_le {K x : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) :
    K / ⌊exp x⌋₊ ≤ 2 * K * exp (-x) := by
  calc K / ⌊exp x⌋₊ ≤ K / (exp x / 2) :=
        div_le_div_of_nonneg_left hK (by positivity) (half_exp_le_floor_exp hx)
    _ = 2 * K * exp (-x) := by rw [exp_neg]; field_simp

lemma div_floor_exp_mul_le {K x y : ℝ} (hK : 0 ≤ K) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    K / (⌊exp x⌋₊ * ⌊exp y⌋₊) ≤ 4 * K * exp (-(x + y)) := by
  calc K / (⌊exp x⌋₊ * ⌊exp y⌋₊) ≤ K / (exp x / 2 * (exp y / 2)) :=
        div_le_div_of_nonneg_left hK (by positivity)
          (mul_le_mul (half_exp_le_floor_exp hx) (half_exp_le_floor_exp hy) (by positivity)
            (Nat.cast_nonneg _))
    _ = 4 * K * exp (-(x + y)) := by rw [exp_neg, exp_add]; field_simp; ring

/-- **Theorem 15.4.1 (Slepian–Wolf, achievability), Section 15.4.1.** Every rate pair with
`R₁ > H(X | Y)`, `R₂ > H(Y | X)` and `R₁ + R₂ > H(X, Y)` is achievable, by random binning. -/
theorem isAchievableSW_of_lt {q : α × β → ℝ} (hq : IsPMF q) {R₁ R₂ : ℝ}
    (h₁ : H[Prod.fst | Prod.snd ; q] < R₁) (h₂ : H[Prod.snd | Prod.fst ; q] < R₂)
    (h₃ : entropy q < R₁ + R₂) : IsAchievableSW q R₁ R₂ := by
  have hne : Nonempty (α × β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  obtain ⟨a, b⟩ := Classical.choice hne
  set H₁ := H[Prod.fst | Prod.snd ; q]
  set H₂ := H[Prod.snd | Prod.fst ; q]
  have hH₁ : 0 ≤ H₁ := condEntropy_nonneg hq _ _
  have hH₂ : 0 ≤ H₂ := condEntropy_nonneg hq _ _
  set A₁ := R₁ - H₁
  set A₂ := R₂ - H₂
  set A₃ := R₁ + R₂ - entropy q
  set ε := min (min A₁ A₂) A₃ / 4 with hε_def
  have hε : 0 < ε := by
    have := lt_min (lt_min (sub_pos.2 h₁) (sub_pos.2 h₂)) (sub_pos.2 h₃)
    positivity
  have hε₁ : H₁ + 4 * ε ≤ R₁ := by
    have := (min_le_left (min A₁ A₂) A₃).trans (min_le_left A₁ A₂)
    linarith
  have hε₂ : H₂ + 4 * ε ≤ R₂ := by
    have := (min_le_left (min A₁ A₂) A₃).trans (min_le_right A₁ A₂)
    linarith
  have hε₃ : entropy q + 4 * ε ≤ R₁ + R₂ := by
    have := min_le_right (min A₁ A₂) A₃
    linarith
  set P : ℕ → ℝ := fun n =>
    (1 - prob (jointIid q n) (jointTypicalSet q n ε)) + 8 * exp (-(n * ε))
  have hP : Tendsto P atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 1 - prob (jointIid q n) (jointTypicalSet q n ε)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_jointTypicalSet hq hε).const_sub 1
    simpa using h1.add ((tendsto_exp_neg_mul_nat hε).const_mul 8)
  have hcode : ∀ n : ℕ, ∃ c : SWCode ⌊exp (n * R₁)⌋₊ ⌊exp (n * R₂)⌋₊ n α β,
      c.errProb q ≤ P n := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hR₁ : 0 ≤ n * R₁ := mul_nonneg hn (by linarith)
    have hR₂ : 0 ≤ n * R₂ := mul_nonneg hn (by linarith)
    have hM₁ : 0 < ⌊exp (n * R₁)⌋₊ := Nat.le_floor (by simpa using one_le_exp hR₁)
    have hM₂ : 0 < ⌊exp (n * R₂)⌋₊ := Nat.le_floor (by simpa using one_le_exp hR₂)
    have h := sum_bins_errProb_le (n := n) hq hM₁ hM₂ ε (fun _ => a, fun _ => b)
    obtain ⟨B, hB⟩ := exists_le_of_sum_mul_le (binLaw_isPMF hM₁ hM₂) h
    refine ⟨_, hB.trans ?_⟩
    have b₁ := div_floor_exp_le (exp_pos (n * (H₁ + 2 * ε))).le hR₁
    have b₂ := div_floor_exp_le (exp_pos (n * (H₂ + 2 * ε))).le hR₂
    have b₃ := div_floor_exp_mul_le (exp_pos (n * (entropy q + ε))).le hR₁ hR₂
    have e : ∀ c r : ℝ, c + ε ≤ r → 2 * exp (n * c) * exp (-(n * r)) ≤ 2 * exp (-(n * ε)) := by
      intro c r hcr
      rw [mul_assoc, ← exp_add]
      gcongr
      nlinarith
    have e₁ := e (H₁ + 2 * ε) R₁ (by linarith)
    have e₂ := e (H₂ + 2 * ε) R₂ (by linarith)
    have e₃ : 4 * exp (n * (entropy q + ε)) * exp (-(n * R₁ + n * R₂)) ≤ 4 * exp (-(n * ε)) := by
      rw [mul_assoc, ← exp_add]
      gcongr
      nlinarith
    simp only [P]
    linarith
  choose c hc using hcode
  exact ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP
    (fun n => (c n).errProb_nonneg hq) hc⟩

/-- **Theorem 15.4.1 (Slepian–Wolf).** For the distributed source coding of `(X, Y)`, i.i.d.
`∼ p(x, y)`, the achievable rate region is `R₁ ≥ H(X | Y)`, `R₂ ≥ H(Y | X)`,
`R₁ + R₂ ≥ H(X, Y)`. -/
theorem swAchievableRegion_eq {q : α × β → ℝ} (hq : IsPMF q) :
    swAchievableRegion q = swRegion q := by
  refine subset_antisymm (closure_minimal (fun R hR => hR.mem_swRegion hq) (isClosed_swRegion q))
    fun R hR => ?_
  obtain ⟨h1, h2, h3⟩ := hR
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have l1 : Tendsto (fun k : ℕ => R.1 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.1 + 0)) :=
    tendsto_const_nhds.add h
  have l2 : Tendsto (fun k : ℕ => R.2 + 1 / ((k : ℝ) + 1)) atTop (𝓝 (R.2 + 0)) :=
    tendsto_const_nhds.add h
  rw [add_zero] at l1 l2
  refine mem_closure_of_tendsto (l1.prodMk_nhds l2) (Eventually.of_forall fun k => ?_)
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  exact isAchievableSW_of_lt hq (by dsimp only; linarith) (by dsimp only; linarith)
    (by dsimp only; linarith)

end InfoTheory
