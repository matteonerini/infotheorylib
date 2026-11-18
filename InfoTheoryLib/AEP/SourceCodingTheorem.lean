/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.AEP.TypicalSet
public import InfoTheoryLib.Entropy.Fano

/-!
# The source coding theorem for block codes

A block code of block length `n` for an i.i.d. source is given by the set `A ⊆ 𝒳ⁿ` of sequences that
are decoded correctly. Its rate is `(1/n) log |A|` and its probability of error is
`Pₑ = Pr{X ∉ A}`. The weak AEP shows that the rate `H(X)` is both achievable, with `Pₑ → 0`, and
optimal: below it, `Pₑ → 1`.

A code that achieves the rate `H(X)` with `Pₑ → 0` produces almost fair bits: its output has almost
the largest possible entropy.

## Main statements

* `exists_blockCode`: the direct part, (5.19)–(5.23).
* `eventually_prob_compl_gt`, `tendsto_prob_compl_of_card_le`: the converse part, (5.24)–(5.27).
* `tendsto_card_typicalSet_div`: the typical set is a vanishing fraction of `𝒳ⁿ`, (5.16).
* `entropy_prefixRV_le_mul_log`, `entropy_prefixRV_eq_mul_log_iff`: `H(Y₁, …, Yₘ) ≤ m log |𝒴|`,
  with equality iff the `Yᵢ` are i.i.d. and uniform, Theorem 5.4.
* `le_entropy_of_blockCode`: the lower bound (5.34)–(5.40) on the entropy of a code's output.
* `tendsto_entropy_div_of_blockCode`: the output of a good code consists of almost fair bits,
  (5.44).

## Implementation notes

Logarithms are natural, so a fair bit carries `log 2` nats.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 5.1 to 5.3
-/

open Real Finset Filter Topology

@[expose] public section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- **The direct part of the source coding theorem, (5.19)–(5.23).** For `n` large, the typical set
`A` has `(1 - ε) e^{n(H - ε)} < |A| ≤ e^{n(H + ε)}` and `Pₑ = Pr{X ∉ A} < ε`. -/
theorem exists_blockCode [DecidableEq α] {p : α → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ A : Finset (Fin n → α),
      (1 - ε) * exp (n * (entropy p - ε)) < A.card ∧ (A.card : ℝ) ≤ exp (n * (entropy p + ε)) ∧
        prob (iidPMF p n) Aᶜ < ε := by
  filter_upwards [eventually_prob_typicalSet_gt hp hε, eventually_card_typicalSet_gt hp hε]
    with n h₁ h₂
  refine ⟨typicalSet p n ε, h₂, card_typicalSet_le hp n ε, ?_⟩
  rw [prob_compl (iidPMF_isPMF hp n)]
  linarith

/-- **The converse part of the source coding theorem, (5.24)–(5.27).** For `ε > 0` and `n` large,
every block code with at most `e^{n(H - ζ)}` codewords has
`Pₑ > 1 - (e^{-n(ζ - ε)} + ε)`. -/
theorem eventually_prob_compl_gt [DecidableEq α] {p : α → ℝ} (hp : IsPMF p) (ζ : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset (Fin n → α),
      (A.card : ℝ) ≤ exp (n * (entropy p - ζ)) →
        1 - (exp (-(n * (ζ - ε))) + ε) < prob (iidPMF p n) Aᶜ := by
  filter_upwards [eventually_prob_typicalSet_gt hp hε] with n hT A hA
  have hμ := iidPMF_isPMF hp n
  set T := typicalSet p n ε
  have h₁ := prob_add_prob_sub_one_le_prob_inter hμ A T
  have h₂ : prob (iidPMF p n) (A ∩ T) ≤ (A ∩ T).card * exp (-(n * (entropy p - ε))) :=
    prob_le_card_mul fun x hx => (mem_typicalSet.1 (mem_inter.1 hx).2).2
  have h₃ : ((A ∩ T).card : ℝ) ≤ A.card := by exact_mod_cast card_le_card inter_subset_left
  have h₄ : (A.card : ℝ) * exp (-(n * (entropy p - ε))) ≤ exp (-(n * (ζ - ε))) := by
    calc (A.card : ℝ) * exp (-(n * (entropy p - ε)))
        ≤ exp (n * (entropy p - ζ)) * exp (-(n * (entropy p - ε))) :=
          mul_le_mul_of_nonneg_right hA (exp_pos _).le
      _ = exp (-(n * (ζ - ε))) := by rw [← exp_add]; congr 1; ring
  have h₅ := mul_le_mul_of_nonneg_right h₃ (exp_pos (-(n * (entropy p - ε)))).le
  rw [prob_compl hμ]
  linarith

/-- **The converse part of the source coding theorem.** Block codes with at most `e^{n(H - ζ)}`
codewords, for a fixed `ζ > 0`, have `Pₑ → 1`. -/
theorem tendsto_prob_compl_of_card_le [DecidableEq α] {p : α → ℝ} (hp : IsPMF p) {ζ : ℝ}
    (hζ : 0 < ζ) {A : ∀ n : ℕ, Finset (Fin n → α)}
    (hA : ∀ᶠ n : ℕ in atTop, ((A n).card : ℝ) ≤ exp (n * (entropy p - ζ))) :
    Tendsto (fun n => prob (iidPMF p n) (A n)ᶜ) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop']
  intro δ hδ
  set ε := min (δ / 2) (ζ / 2) with hε_def
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεζ : ε ≤ ζ / 2 := min_le_right _ _
  have hlim : Tendsto (fun n : ℕ => exp (-(n * (ζ - ε)))) atTop (𝓝 0) := by
    refine tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)
  have hev := (eventually_prob_compl_gt hp ζ hε).and
    ((hA.and (hlim.eventually (gt_mem_nhds (show 0 < δ / 2 by linarith)))))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hN n hn.le
  have h₄ := h₁ (A n) h₂
  have h₅ := prob_le_one (iidPMF_isPMF hp n) (A n)ᶜ
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **(5.16)** If `H(X) + ε < log |𝒳|`, the typical set is a vanishing fraction of `𝒳ⁿ`. -/
theorem tendsto_card_typicalSet_div {p : α → ℝ} (hp : IsPMF p) {ε : ℝ}
    (hε : entropy p + ε < log (Fintype.card α)) :
    Tendsto (fun n : ℕ => ((typicalSet p n ε).card : ℝ) / (Fintype.card α : ℝ) ^ n) atTop
      (𝓝 0) := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hp
  have hlim : Tendsto (fun n : ℕ => exp (-(n * (log (Fintype.card α) - (entropy p + ε))))) atTop
      (𝓝 0) := by
    refine tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  have hpow : (Fintype.card α : ℝ) ^ n = exp (n * log (Fintype.card α)) := by
    rw [← rpow_natCast, rpow_def_of_pos hc, mul_comm]
  rw [hpow, div_le_iff₀ (exp_pos _), ← exp_add]
  calc ((typicalSet p n ε).card : ℝ) ≤ exp (n * (entropy p + ε)) := card_typicalSet_le hp n ε
    _ = _ := by congr 1; ring

variable {Ω : Type*} [Fintype Ω]

/-- **Theorem 5.4 (the bound).** `H(Y₁, …, Yₘ) ≤ m log |𝒴|`, which is `m` bits for a binary
sequence. -/
theorem entropy_prefixRV_le_mul_log {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : ℕ → Ω → α) (m : ℕ) :
    H[prefixRV Y m ; μ] ≤ m * log (Fintype.card α) := by
  refine (entropy_prefixRV_le_sum hμ Y m).trans ?_
  calc ∑ i ∈ range m, H[Y i ; μ] ≤ ∑ _i ∈ range m, log (Fintype.card α) :=
        sum_le_sum fun i _ => entropyRV_le_log_card hμ (Y i)
    _ = m * log (Fintype.card α) := by simp

/-- **Theorem 5.4 (the equality case).** `H(Y₁, …, Yₘ) = m log |𝒴|` iff the `Yᵢ` are independent and
uniform on `𝒴`. -/
theorem entropy_prefixRV_eq_mul_log_iff {μ : Ω → ℝ} (hμ : IsPMF μ) (Y : ℕ → Ω → α) (m : ℕ) :
    H[prefixRV Y m ; μ] = m * log (Fintype.card α) ↔
      IndepFamily μ Y m ∧ ∀ i ∈ range m, dist μ (Y i) = uniformPMF α := by
  have hle := entropy_prefixRV_le_sum hμ Y m
  have hle' : ∀ i ∈ range m, H[Y i ; μ] ≤ log (Fintype.card α) :=
    fun i _ => entropyRV_le_log_card hμ (Y i)
  have hsum : ∑ _i ∈ range m, log (Fintype.card α) = m * log (Fintype.card α) := by simp
  have hsum' := sum_le_sum hle'
  rw [hsum] at hsum'
  constructor
  · intro h
    have h₁ : H[prefixRV Y m ; μ] = ∑ i ∈ range m, H[Y i ; μ] := by linarith
    have h₂ : ∑ i ∈ range m, H[Y i ; μ] = ∑ _i ∈ range m, log (Fintype.card α) := by linarith
    refine ⟨(entropy_prefixRV_eq_sum_iff hμ Y m).1 h₁, fun i hi => ?_⟩
    exact (entropy_eq_log_card_iff (hμ.dist (Y i))).1 ((sum_eq_sum_iff_of_le hle').1 h₂ i hi)
  · rintro ⟨h₁, h₂⟩
    rw [(entropy_prefixRV_eq_sum_iff hμ Y m).2 h₁, ← hsum]
    exact sum_congr rfl fun i hi =>
      (entropy_eq_log_card_iff (hμ.dist (Y i))).2 (h₂ i hi)

/-- **(5.34)–(5.40)** Let a block code encode `X = (X₁, …, Xₙ)` into `Y = f(X)`, with decoder `g`,
and let `Pₑ = Pr{g(Y) ≠ X}`. Then `H(Y) ≥ n (H(X) - Pₑ log |𝒳|) - log 2`. -/
theorem le_entropy_of_blockCode {β : Type*} [Fintype β] {p : α → ℝ} (hp : IsPMF p) {n : ℕ}
    (f : (Fin n → α) → β) (g : β → Fin n → α) :
    n * (entropy p - errProb (iidPMF p n) id f g * log (Fintype.card α)) - log 2 ≤
      H[f ; iidPMF p n] := by
  have hμ := iidPMF_isPMF hp n
  have h₁ := fano_weak hμ id f g
  have h₂ : log (Fintype.card (Fin n → α)) = n * log (Fintype.card α) := by simp
  have h₃ : H[(id : (Fin n → α) → Fin n → α) ; iidPMF p n] = n * entropy p := by
    rw [entropyRV, dist_id, entropy_iidPMF hp]
  have h₄ := mutualInfo_eq_entropy_sub_condEntropy hμ id f
  have h₅ := mutualInfo_eq_entropy_sub_condEntropy' hμ id f
  have h₆ := condEntropy_nonneg hμ f id
  rw [h₂] at h₁
  have h₇ : n * (entropy p - errProb (iidPMF p n) id f g * log (Fintype.card α)) =
      n * entropy p - errProb (iidPMF p n) id f g * (n * log (Fintype.card α)) := by ring
  linarith

/-- **(5.42)–(5.44) (almost fair bits).** Let a sequence of block codes encode `(X₁, …, Xₙ)` into a
binary sequence of length `m n`, with `m n log 2 / n → H(X) > 0` and `Pₑ → 0`. Then
`H(Y) / (m n log 2) → 1`: the output `Y` has almost the largest possible entropy. -/
theorem tendsto_entropy_div_of_blockCode {p : α → ℝ} (hp : IsPMF p) (hH : 0 < entropy p)
    {m : ℕ → ℕ} (hm : Tendsto (fun n : ℕ => m n * log 2 / n) atTop (𝓝 (entropy p)))
    (f : ∀ n : ℕ, (Fin n → α) → Fin (m n) → Bool) (g : ∀ n : ℕ, (Fin (m n) → Bool) → Fin n → α)
    (hP : Tendsto (fun n => errProb (iidPMF p n) id (f n) (g n)) atTop (𝓝 0)) :
    Tendsto (fun n => H[f n ; iidPMF p n] / (m n * log 2)) atTop (𝓝 1) := by
  have hupper : ∀ n, H[f n ; iidPMF p n] ≤ m n * log 2 := fun n => by
    have := entropyRV_le_log_card (iidPMF_isPMF hp n) (f n)
    simpa using this
  have hlower : Tendsto (fun n : ℕ => (entropy p - errProb (iidPMF p n) id (f n) (g n) *
      log (Fintype.card α)) - log 2 / n) atTop (𝓝 (entropy p)) := by
    have h₁ := tendsto_const_nhds (x := entropy p) (f := (atTop : Filter ℕ))
    have h₂ := hP.mul_const (log (Fintype.card α))
    have h₃ : Tendsto (fun n : ℕ => log 2 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using (h₁.sub h₂).sub h₃
  have hrate : Tendsto (fun n : ℕ => H[f n ; iidPMF p n] / n) atTop (𝓝 (entropy p)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hm ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have := le_entropy_of_blockCode hp (f n) (g n)
      rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
      linarith
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      exact div_le_div_of_nonneg_right (hupper n) hn'.le
  have hdiv := hrate.div hm hH.ne'
  rw [div_self hH.ne'] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  exact div_div_div_cancel_right₀ hn' _ _

end InfoTheory
