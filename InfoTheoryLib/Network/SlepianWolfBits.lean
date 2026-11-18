/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.SlepianWolf

/-!
# The Slepian–Wolf theorem in bits

In their lecture notes, El Gamal and Kim measure the rates in bits, with index sets
`[1 : 2^{nR}) = {1, …, 2^⌊nR⌋}`. This file bridges the Slepian–Wolf theorem of Chapter 15 of Cover
and Thomas, in nats with `⌊e^{nR}⌋` indices, to this form.

## Main definitions

* `IsAchievableSWBits q R₁ R₂`, `swOptimalRegionBits q`: achievable rates and the optimal rate
  region.
* `swRegionBits q`: `R₁ ≥ H(X₁ | X₂)`, `R₂ ≥ H(X₂ | X₁)`, `R₁ + R₂ ≥ H(X₁, X₂)`, in bits.

## Main statements

* `IsAchievableSWBits.mem_swRegionBits`: the converse.
* `isAchievableSWBits_of_lt`: achievability.
* `swOptimalRegionBits_eq`: **the Slepian–Wolf theorem of Lecture 11**.
* `entropy_mem_swRegionBits`: the inner bound `R₁ ≥ H(X₁)`, `R₂ ≥ H(X₂)`.
* `corner_mem_swRegionBits`: the corner point `(H(X₁ | X₂), H(X₂))`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 11
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Lecture 11 of [elgamal2010], page 11-3.** A rate pair, in bits per source symbol, is
achievable if there are distributed source codes with the index sets `[1 : 2^{nRⱼ})` whose
probability of error tends to `0`. -/
def IsAchievableSWBits (q : α × β → ℝ) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ ∃ c : ∀ n : ℕ, SWCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β,
    Tendsto (fun n => (c n).errProb q) atTop (𝓝 0)

/-- **Lecture 11 of [elgamal2010], page 11-3.** The optimal rate region: the closure of the set of
achievable rate pairs. -/
def swOptimalRegionBits (q : α × β → ℝ) : Set (ℝ × ℝ) := closure {R | IsAchievableSWBits q R.1 R.2}

/-- **Lecture 11 of [elgamal2010], page 11-9.** The Slepian–Wolf region in bits. -/
def swRegionBits (q : α × β → ℝ) : Set (ℝ × ℝ) :=
  {R | H[Prod.fst | Prod.snd ; q] / log 2 ≤ R.1 ∧ H[Prod.snd | Prod.fst ; q] / log 2 ≤ R.2 ∧
    entropy q / log 2 ≤ R.1 + R.2}

lemma isClosed_swRegionBits (q : α × β → ℝ) : IsClosed (swRegionBits q) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_const (continuous_fst.add continuous_snd)))

/-- `log 2^⌊nR⌋ ≤ n R log 2`. -/
lemma log_two_pow_floor_le (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    log ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) ≤ n * (R * log 2) := by
  have hl := log_pos one_lt_two
  push_cast
  rw [log_pow]
  have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hR)
  nlinarith

/-- `2^⌊nR⌋ ≥ e^{nR log 2 - log 2}`. -/
lemma exp_le_two_pow_floor (n : ℕ) (R : ℝ) :
    exp (n * (R * log 2) - log 2) ≤ ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) := by
  have hl := log_pos one_lt_two
  have hfl : (n : ℝ) * R < ⌊(n : ℝ) * R⌋₊ + 1 := Nat.lt_floor_add_one _
  push_cast
  rw [← rpow_natCast, rpow_def_of_pos two_pos]
  refine exp_le_exp.2 ?_
  nlinarith

/-- **Lecture 11, pages 11-4 and 11-5.** The converse of the Slepian–Wolf theorem. -/
theorem IsAchievableSWBits.mem_swRegionBits {q : α × β → ℝ} (hq : IsPMF q) {R₁ R₂ : ℝ}
    (h : IsAchievableSWBits q R₁ R₂) : (R₁, R₂) ∈ swRegionBits q := by
  obtain ⟨h₁, h₂, c, hc⟩ := h
  have hl := log_pos one_lt_two
  have hne : Nonempty (α × β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  have hpos : ∀ {k : ℕ}, (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := fun {k} => by positivity
  refine ⟨?_, ?_, ?_⟩
  · refine (div_le_iff₀ hl).2 (le_of_sw_bound (L := log (Fintype.card α * Fintype.card β)) hc
      fun n _ => ?_)
    have h3 := (c n).mul_condEntropy_fst_le hq
    have h4 := log_two_pow_floor_le n h₁
    linarith
  · refine (div_le_iff₀ hl).2 (le_of_sw_bound (L := log (Fintype.card α * Fintype.card β)) hc
      fun n _ => ?_)
    have h3 := (c n).mul_condEntropy_snd_le hq
    have h4 := log_two_pow_floor_le n h₂
    linarith
  · refine (div_le_iff₀ hl).2 (le_of_sw_bound (L := log (Fintype.card α * Fintype.card β)) hc
      fun n _ => ?_)
    have h3 := (c n).mul_entropy_le hq
    rw [log_mul hpos.ne' hpos.ne'] at h3
    have h4 := log_two_pow_floor_le n h₁
    have h5 := log_two_pow_floor_le n h₂
    simp only [add_mul, mul_add] at h3 ⊢
    nlinarith

/-- A code with fewer indices is a code with more indices, with the same probability of error. -/
private lemma exists_code_castLE {M₁ M₂ M₁' M₂' n : ℕ} (c : SWCode M₁' M₂' n α β)
    (h₁ : M₁' ≤ M₁) (h₂ : M₂' ≤ M₂) (q : α × β → ℝ) (d : (Fin n → α) × (Fin n → β)) :
    ∃ c' : SWCode M₁ M₂ n α β, c'.errProb q = c.errProb q := by
  classical
  refine ⟨⟨fun x => Fin.castLE h₁ (c.enc₁ x), fun y => Fin.castLE h₂ (c.enc₂ y), fun w =>
    if h : (w.1 : ℕ) < M₁' ∧ (w.2 : ℕ) < M₂' then c.dec (⟨w.1, h.1⟩, ⟨w.2, h.2⟩) else d⟩, ?_⟩
  simp only [SWCode.errProb, SWCode.index]
  refine sum_congr rfl fun z _ => ?_
  by_cases hd : c.dec (c.enc₁ z.1, c.enc₂ z.2) = z <;> simp [hd]

/-- `⌊e^{nR'}⌋ ≤ 2^⌊nR⌋` as soon as `log 2 ≤ n (R log 2 - R')`. -/
private lemma floor_exp_le_two_pow {n : ℕ} {R R' : ℝ} (h : log 2 ≤ n * (R * log 2 - R'))
    (hR : 0 ≤ R) : ⌊exp (n * R')⌋₊ ≤ 2 ^ ⌊n * R⌋₊ := by
  have hl := log_pos one_lt_two
  have hx : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR
  have hfl : (n : ℝ) * R < ⌊(n : ℝ) * R⌋₊ + 1 := Nat.lt_floor_add_one _
  have hreal : ((⌊exp (n * R')⌋₊ : ℕ) : ℝ) ≤ ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) := by
    refine (Nat.floor_le (exp_pos _).le).trans ?_
    push_cast
    rw [← rpow_natCast, rpow_def_of_pos two_pos]
    refine exp_le_exp.2 ?_
    nlinarith
  exact_mod_cast hreal

/-- **The Slepian–Wolf theorem of Lecture 11, achievability.** A pair of rates in the interior of
the region is achievable. -/
theorem isAchievableSWBits_of_lt {q : α × β → ℝ} (hq : IsPMF q) {R₁ R₂ : ℝ}
    (h₁ : H[Prod.fst | Prod.snd ; q] / log 2 < R₁) (h₂ : H[Prod.snd | Prod.fst ; q] / log 2 < R₂)
    (h₃ : entropy q / log 2 < R₁ + R₂) : IsAchievableSWBits q R₁ R₂ := by
  have hl := log_pos one_lt_two
  have hne : Nonempty (α × β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  obtain ⟨⟨a, b⟩⟩ := hne
  have g₁ := (div_lt_iff₀ hl).1 h₁
  have g₂ := (div_lt_iff₀ hl).1 h₂
  have g₃ := (div_lt_iff₀ hl).1 h₃
  have n₁ : 0 ≤ H[Prod.fst | Prod.snd ; q] / log 2 := div_nonneg (condEntropy_nonneg hq _ _) hl.le
  have n₂ : 0 ≤ H[Prod.snd | Prod.fst ; q] / log 2 := div_nonneg (condEntropy_nonneg hq _ _) hl.le
  -- A gap `t` between the entropies and the rates.
  obtain ⟨t, ht, t₁, t₂, t₃⟩ : ∃ t : ℝ, 0 < t ∧ H[Prod.fst | Prod.snd ; q] < R₁ * log 2 - t ∧
      H[Prod.snd | Prod.fst ; q] < R₂ * log 2 - t ∧
      entropy q < (R₁ * log 2 - t) + (R₂ * log 2 - t) := by
    refine ⟨min (R₁ * log 2 - H[Prod.fst | Prod.snd ; q]) (min (R₂ * log 2 -
      H[Prod.snd | Prod.fst ; q]) ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2)) / 2, ?_, ?_, ?_, ?_⟩
    · refine half_pos (lt_min (by linarith) (lt_min (by linarith) ?_))
      have : entropy q < (R₁ + R₂) * log 2 := g₃
      linarith [add_mul R₁ R₂ (log 2)]
    · have := min_le_left (R₁ * log 2 - H[Prod.fst | Prod.snd ; q]) (min (R₂ * log 2 -
        H[Prod.snd | Prod.fst ; q]) ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2))
      have hp : 0 < min (R₁ * log 2 - H[Prod.fst | Prod.snd ; q]) (min (R₂ * log 2 -
        H[Prod.snd | Prod.fst ; q]) ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2)) :=
        lt_min (by linarith) (lt_min (by linarith) (by linarith [add_mul R₁ R₂ (log 2)]))
      linarith
    · have h1 := min_le_right (R₁ * log 2 - H[Prod.fst | Prod.snd ; q]) (min (R₂ * log 2 -
        H[Prod.snd | Prod.fst ; q]) ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2))
      have h2 := min_le_left (R₂ * log 2 - H[Prod.snd | Prod.fst ; q])
        ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2)
      have hp : 0 < min (R₁ * log 2 - H[Prod.fst | Prod.snd ; q]) (min (R₂ * log 2 -
        H[Prod.snd | Prod.fst ; q]) ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2)) :=
        lt_min (by linarith) (lt_min (by linarith) (by linarith [add_mul R₁ R₂ (log 2)]))
      linarith
    · have h1 := min_le_right (R₁ * log 2 - H[Prod.fst | Prod.snd ; q]) (min (R₂ * log 2 -
        H[Prod.snd | Prod.fst ; q]) ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2))
      have h2 := min_le_right (R₂ * log 2 - H[Prod.snd | Prod.fst ; q])
        ((R₁ * log 2 + R₂ * log 2 - entropy q) / 2)
      linarith
  obtain ⟨c, hc⟩ := isAchievableSW_of_lt hq t₁ t₂ t₃
  have hR₁ : 0 ≤ R₁ := n₁.trans h₁.le
  have hR₂ : 0 ≤ R₂ := n₂.trans h₂.le
  have hsub : ∀ n : ℕ, ∃ c' : SWCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β,
      log 2 ≤ n * t → c'.errProb q ≤ (c n).errProb q := fun n => by
    by_cases hn : log 2 ≤ n * t
    · have e₁ : log 2 ≤ n * (R₁ * log 2 - (R₁ * log 2 - t)) := by simpa using hn
      have e₂ : log 2 ≤ n * (R₂ * log 2 - (R₂ * log 2 - t)) := by simpa using hn
      obtain ⟨c', hc'⟩ := exists_code_castLE (c n) (floor_exp_le_two_pow e₁ hR₁)
        (floor_exp_le_two_pow e₂ hR₂) q (fun _ => a, fun _ => b)
      exact ⟨c', fun _ => hc'.le⟩
    · exact ⟨⟨fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩, fun _ => (fun _ => a,
        fun _ => b)⟩, fun h' => absurd h' hn⟩
  choose c' hc' using hsub
  refine ⟨hR₁, hR₂, c', tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Eventually.of_forall fun n => (c' n).errProb_nonneg hq) ?_⟩
  filter_upwards [eventually_ge_atTop ⌈log 2 / t⌉₊] with n hn
  exact hc' n ((div_le_iff₀ ht).1 (Nat.ceil_le.1 hn))

/-- **The Slepian–Wolf theorem (Lecture 11 of [elgamal2010], page 11-9).** The optimal rate region
of distributed lossless source coding of a 2-DMS is `R₁ ≥ H(X₁ | X₂)`, `R₂ ≥ H(X₂ | X₁)`,
`R₁ + R₂ ≥ H(X₁, X₂)`, in bits. -/
theorem swOptimalRegionBits_eq {q : α × β → ℝ} (hq : IsPMF q) :
    swOptimalRegionBits q = swRegionBits q := by
  refine subset_antisymm (closure_minimal (fun R hR => ?_) (isClosed_swRegionBits q)) ?_
  · exact IsAchievableSWBits.mem_swRegionBits hq hR
  · rintro ⟨R₁, R₂⟩ ⟨h₁, h₂, h₃⟩
    dsimp only at h₁ h₂ h₃
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ => (R₁ + 1 / ((n : ℝ) + 1), R₂ + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 (R₁, R₂)) := by
      have l₁ := (tendsto_const_nhds (x := R₁)).add ht
      have l₂ := (tendsto_const_nhds (x := R₂)).add ht
      rw [add_zero] at l₁ l₂
      exact l₁.prodMk_nhds l₂
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact isAchievableSWBits_of_lt hq (by linarith) (by linarith) (by linarith)

/-- **Lecture 11, page 11-4.** The inner bound by separate lossless coding: `(H(X₁), H(X₂))` is in
the region. -/
theorem entropy_mem_swRegionBits {q : α × β → ℝ} (hq : IsPMF q) :
    (H[Prod.fst ; q] / log 2, H[Prod.snd ; q] / log 2) ∈ swRegionBits q := by
  have hl := log_pos one_lt_two
  have h1 := condEntropy_le_entropy hq (Prod.fst : α × β → α) Prod.snd
  have h2 := condEntropy_le_entropy hq (Prod.snd : α × β → β) Prod.fst
  have hc := chain_rule hq (Prod.fst : α × β → α) Prod.snd
  have he : H[pair Prod.fst Prod.snd ; q] = entropy q := by
    rw [entropyRV, dist_pair_fst_snd]
  refine ⟨div_le_div_of_nonneg_right h1 hl.le, div_le_div_of_nonneg_right h2 hl.le, ?_⟩
  simp only
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hl.le
  rw [← he, hc]
  linarith

/-- **Lecture 11, page 11-7.** The corner point `(H(X₁ | X₂), H(X₂))` is in the region, with the sum
rate `H(X₁, X₂)`. -/
theorem corner_mem_swRegionBits {q : α × β → ℝ} (hq : IsPMF q) :
    (H[Prod.fst | Prod.snd ; q] / log 2, H[Prod.snd ; q] / log 2) ∈ swRegionBits q := by
  have hl := log_pos one_lt_two
  have h2 := condEntropy_le_entropy hq (Prod.snd : α × β → β) Prod.fst
  have hc := chain_rule hq (Prod.snd : α × β → β) Prod.fst
  have he : H[pair Prod.snd Prod.fst ; q] = entropy q := by
    have e : H[pair Prod.snd Prod.fst ; q] = H[pair Prod.fst Prod.snd ; q] :=
      entropyRV_eq_of_injective q Prod.swap Prod.swap_injective fun _ => rfl
    rw [e, entropyRV, dist_pair_fst_snd]
  refine ⟨le_rfl, div_le_div_of_nonneg_right h2 hl.le, ?_⟩
  simp only
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ hl.le
  rw [← he, hc]
  linarith

end InfoTheory
