/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.LempelZiv
public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.Entropy.Conditional
public import InfoTheoryLib.Probability.Channel
public import InfoTheoryLib.StochasticProcess.Basic
public import InfoTheoryLib.Statistics.LargeDeviations

/-!
# Optimality of tree-structured Lempel–Ziv coding

The proof of the asymptotic optimality of LZ78 rests on two deterministic facts about a distinct
parsing `y₁, …, y_c` of a binary string `x₁ ⋯ xₙ`:

* there are few phrases, `c ≤ n / ((1 - εₙ) log₂ n)` with `εₙ → 0` (Lemma 13.5.3), since there
  are only `2ˡ` binary strings of length `l`;
* the probability of `x` under any `k`-th order Markov model `Q_k` is small,
  `log Q_k(x | s₁) ≤ -∑_{l,s} c_{ls} log c_{ls}`, where `c_{ls}` counts the phrases of length `l`
  preceded by the state `s` (Ziv's inequality, Lemma 13.5.5).

With the bound `H(U) ≤ (μ + 1) log (μ + 1) - μ log μ` on the entropy of an integer random
variable of mean `μ` (Lemma 13.5.4), they give `c log c ≤ -log Q_k(x | s₁) + o(n)`, uniformly
over all strings and all Markov models (13.125). For a sequence along which
`-(1/n) log Q_k(x₁ ⋯ xₙ | s₁)` converges to `h` (for an ergodic source, `h` is the entropy of the
`k`-th order Markov approximation, by the ergodic theorem) the number of phrases satisfies
`lim sup c(n) log c(n) / n ≤ h` (Theorem 13.5.2), and so does the LZ78 code length per symbol
(Theorem 13.5.3).

## Main definitions

* `shiftState s a`, `advanceState s w`: the last `k` bits, updated by a bit or a string.
* `markovProb K s w`: the probability `Q_k(w | s)` of the string `w` under the `k`-th order Markov
  kernel `K`, started in the state `s` (13.98).
* `phraseState K s ws i`: the state `sᵢ` preceding the `i`-th phrase.
* `phraseCount s ws κ`: the number `c_{ls}` of phrases of length `l` preceded by the state `s`,
  for `κ = (l, s)`.

## Main statements

* `mul_length_le_of_nodup`, `length_mul_le_of_nodup`: **Lemma 13.5.3**, in the forms
  `(m + 1) c ≤ n + 2^{m+2}` for every `m` and `c (log₂ n - log₂ log₂ n - 4) ≤ n`.
* `exists_length_le_mul_of_nodup`: `c ≤ ε n` for `n` large, uniformly.
* `entropy_le_of_mean`: **Lemma 13.5.4**.
* `log_markovProb_le`: **Lemma 13.5.5 (Ziv's inequality)**, (13.104)–(13.111).
* `length_mul_log_length_le`: **(13.113)–(13.123)**,
  `c log c ≤ -log Q_k(x | s₁) + c (k log 2 + log (n/c) + 1 + c/n)`.
* `exists_length_mul_log_length_le`: **(13.124)–(13.125)**, uniformly in the string and the
  model, `c log c / n ≤ -log Q_k(x | s₁) / n + ε` for `n` large.
* `eventually_length_mul_log_length_le`: **Theorem 13.5.2**, for a sequence.
* `exists_lz78Length_le`, `eventually_lz78Length_le`: **Theorem 13.5.3**, the same bounds for the
  length of the LZ78 code.

## Implementation notes

All statements are deterministic: they hold for every string and every Markov model. The
convergence `-(1/n) log Q_k(X₁ ⋯ Xₙ | X_{-(k-1)}⁰) → H(X₀ | X_{-1}, …, X_{-k})` with probability
one (13.99)–(13.101), which requires the ergodic theorem, and the limit `k → ∞` (13.128) are not
formalized; Theorem 13.5.2 is stated for a sequence along which the normalized log-likelihood
converges. Strings are `List Bool`, states are `Fin k → Bool` (oldest bit first), and logarithms
are natural, so the LZ78 length in bits is multiplied by `log 2`. The positivity assumption
`Q_k(x | s₁) > 0` keeps `log Q_k` finite.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 13.5.2
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Lemma 13.5.3: the number of phrases of a distinct parsing -/

/-- `∑_{j ≤ m} 2ʲ = 2^{m+1} - 1`. -/
lemma sum_range_two_pow_add_one (m : ℕ) : ∑ j ∈ range m, 2 ^ j + 1 = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ, pow_succ]; omega

/-- `∑_{j ≤ m} (m + 1 - j) 2ʲ ≤ 2^{m+2}`. -/
lemma sum_range_sub_mul_two_pow_le (m : ℕ) :
    ∑ j ∈ range (m + 1), (m + 1 - j) * 2 ^ j + (m + 3) ≤ 2 ^ (m + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h : ∑ j ∈ range (m + 2), (m + 2 - j) * 2 ^ j =
        ∑ j ∈ range (m + 1), (m + 1 - j) * 2 ^ j + ∑ j ∈ range (m + 2), 2 ^ j := by
      rw [sum_range_succ (fun j => (m + 2 - j) * 2 ^ j), sum_range_succ (fun j => 2 ^ j),
        ← add_assoc, ← sum_add_distrib]
      congr 1
      · refine sum_congr rfl fun j hj => ?_
        have := mem_range.1 hj
        rw [show m + 2 - j = (m + 1 - j) + 1 by omega, add_mul, one_mul]
      · simp
    have hg := sum_range_two_pow_add_one (m + 2)
    rw [h, show m + 1 + 2 = m + 3 by ring, pow_succ]
    rw [show m + 2 = m + 2 from rfl] at ih
    omega

/-- The number of distinct binary strings of length `j` is at most `2ʲ`. -/
lemma card_filter_length_le (S : Finset (List Bool)) (j : ℕ) :
    (S.filter fun w => w.length = j).card ≤ 2 ^ j := by
  have hsub : S.filter (fun w => w.length = j) ⊆
      univ.image fun w : Fin j → Bool => List.ofFn w := by
    intro w hw
    obtain ⟨-, hl⟩ := mem_filter.1 hw
    subst hl
    exact mem_image.2 ⟨fun i => w[i], mem_univ _, List.ofFn_getElem⟩
  calc (S.filter fun w => w.length = j).card ≤ (univ.image fun w : Fin j → Bool =>
        List.ofFn w).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin j → Bool)).card := card_image_le
    _ = 2 ^ j := by simp

/-- **Lemma 13.5.3, (13.85)–(13.87).** A list of `c` distinct binary strings of total length `n`
has `(m + 1) c ≤ n + 2^{m+2}` for every `m`: the strings shorter than `m + 1` are few. -/
theorem mul_length_le_of_nodup {ws : List (List Bool)} (hnd : ws.Nodup) (m : ℕ) :
    (m + 1) * ws.length ≤ ws.flatten.length + 2 ^ (m + 2) := by
  set S := ws.toFinset
  have hc : S.card = ws.length := List.toFinset_card_of_nodup hnd
  have hn : ∑ w ∈ S, w.length = ws.flatten.length := by
    rw [List.length_flatten, List.sum_toFinset _ hnd]
  -- `m + 1 ≤ |w| + (m + 1 - |w|)` for every string.
  have h1 : (m + 1) * S.card ≤ ∑ w ∈ S, w.length + ∑ w ∈ S, (m + 1 - w.length) := by
    rw [← sum_add_distrib, mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun w _ => by omega
  -- Group the strings by length.
  have h2 : ∑ w ∈ S, (m + 1 - w.length) ≤ ∑ j ∈ range (m + 1), (m + 1 - j) * 2 ^ j := by
    have hsplit : ∑ w ∈ S, (m + 1 - w.length) =
        ∑ w ∈ S.filter (fun w => w.length < m + 1), (m + 1 - w.length) := by
      rw [sum_filter]
      refine sum_congr rfl fun w _ => ?_
      split_ifs with h
      · rfl
      · omega
    rw [hsplit, ← sum_fiberwise_of_maps_to (g := List.length) (t := range (m + 1))
      (fun w hw => mem_range.2 (mem_filter.1 hw).2)]
    refine sum_le_sum fun j hj => ?_
    rw [sum_congr rfl fun w hw => by rw [(mem_filter.1 hw).2], sum_const, smul_eq_mul, mul_comm]
    refine Nat.mul_le_mul_left _ ((card_le_card fun w hw => ?_).trans (card_filter_length_le S j))
    simp only [mem_filter] at hw ⊢
    exact ⟨hw.1.1, hw.2⟩
  have h3 := sum_range_sub_mul_two_pow_le m
  rw [hc, hn] at h1
  omega

/-- **Lemma 13.5.3, (13.84), (13.88)–(13.96).** A distinct parsing of a binary string of length
`n` into `c` phrases has `c ≤ n / ((1 - εₙ) log₂ n)`, `εₙ = (log₂ log₂ n + 4) / log₂ n`, that is,
`c (log₂ n - log₂ log₂ n - 4) ≤ n`, whenever `log₂ log₂ n + 4 < log₂ n`. -/
theorem length_mul_le_of_nodup {ws : List (List Bool)} (hnd : ws.Nodup)
    (hL : logb 2 (logb 2 ws.flatten.length) + 4 < logb 2 ws.flatten.length) :
    (ws.length : ℝ) * (logb 2 ws.flatten.length - logb 2 (logb 2 ws.flatten.length) - 4) ≤
      ws.flatten.length := by
  have hn2 : 2 ≤ ws.flatten.length := by
    by_contra h
    push Not at h
    have h0 : logb 2 (ws.flatten.length : ℝ) = 0 := by
      interval_cases h' : ws.flatten.length <;> simp
    rw [h0] at hL
    norm_num at hL
  set n : ℝ := (ws.flatten.length : ℝ)
  set c : ℝ := (ws.length : ℝ)
  set L := logb 2 n
  set y := L - logb 2 L
  have hn0 : 0 < n := by simp only [n]; positivity
  have hL1 : 1 ≤ L := by
    rw [le_logb_iff_rpow_le (by norm_num) hn0, rpow_one]
    simp only [n]
    exact_mod_cast hn2
  have hlogL : 0 ≤ logb 2 L := logb_nonneg (by norm_num) hL1
  have hy : 4 < y := by simp only [y]; linarith
  -- Choose `m + 2 = ⌊y⌋`.
  set m := ⌊y⌋₊ - 2
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hfl' : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have hm2 : ((m + 2 : ℕ) : ℝ) = ⌊y⌋₊ := by
    have : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_num; linarith)
    simp only [m]
    rw [Nat.sub_add_cancel this]
  have hpow : ((2 ^ (m + 2) : ℕ) : ℝ) ≤ n / L := by
    have h1 : ((2 ^ (m + 2) : ℕ) : ℝ) = (2 : ℝ) ^ ((m + 2 : ℕ) : ℝ) := by
      rw [rpow_natCast]
      push_cast
      ring
    rw [h1, hm2]
    calc (2 : ℝ) ^ (⌊y⌋₊ : ℝ) ≤ 2 ^ y := rpow_le_rpow_of_exponent_le (by norm_num) hfl
      _ = n / L := by
        rw [rpow_sub (by norm_num), rpow_logb (by norm_num) (by norm_num) hn0,
          rpow_logb (by norm_num) (by norm_num) (by linarith)]
  have hmain := mul_length_le_of_nodup hnd m
  have hmain' : ((m : ℝ) + 1) * c ≤ n + n / L := by
    have := (Nat.cast_le (α := ℝ)).2 hmain
    have hp' : (2 : ℝ) ^ (m + 2) ≤ n / L := by exact_mod_cast hpow
    push_cast at this
    exact this.trans (by linarith)
  have hm1 : y - 2 < (m : ℝ) + 1 := by
    have : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    linarith
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hy2 : (y - 2) * c ≤ n + n / L :=
    (mul_le_mul_of_nonneg_right hm1.le hc0).trans hmain'
  change c * (y - 4) ≤ n
  rcases le_or_gt (n / L) (2 * c) with h | h
  · nlinarith
  · have hcL : c * L < n / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      rw [lt_div_iff₀ (by linarith)] at h
      linarith
    have : c * (y - 4) ≤ c * L := mul_le_mul_of_nonneg_left (by simp only [y]; linarith) hc0
    linarith

/-- **Lemma 13.5.3 (asymptotic form).** For every `ε > 0` and `n` large enough, every distinct
parsing of a binary string of length `n` has at most `ε n` phrases. -/
theorem exists_length_le_mul_of_nodup {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ ws : List (List Bool), ws.Nodup → N ≤ ws.flatten.length →
      (ws.length : ℝ) ≤ ε * ws.flatten.length := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / ε)
  refine ⟨2 ^ (m + 2), fun ws hnd hN => ?_⟩
  have h := mul_length_le_of_nodup hnd m
  have h' : ((m : ℝ) + 1) * ws.length ≤ 2 * ws.flatten.length := by
    have := (Nat.cast_le (α := ℝ)).2 (h.trans (by omega : _ ≤ 2 * ws.flatten.length))
    push_cast at this
    exact this
  have hm' : 2 ≤ ε * ((m : ℝ) + 1) := by
    rw [div_lt_iff₀ hε] at hm
    nlinarith
  have hn := Nat.cast_nonneg (α := ℝ) ws.flatten.length
  have hc := Nat.cast_nonneg (α := ℝ) ws.length
  nlinarith

/-! ### Lemma 13.5.4: maximum entropy of an integer random variable -/

/-- **Lemma 13.5.4, (13.97).** A distribution `p` on values `z(g) ∈ ℕ` (with `z` injective), of
mean `μ`, has `H(p) ≤ (μ + 1) log (μ + 1) - μ log μ`, the entropy of the geometric distribution
of mean `μ`. -/
theorem entropy_le_of_mean {γ : Type*} [Fintype γ] {p : γ → ℝ} (hp : IsPMF p) {z : γ → ℕ}
    (hz : Function.Injective z) :
    entropy p ≤ ((∑ g, p g * z g) + 1) * log ((∑ g, p g * z g) + 1) -
      (∑ g, p g * z g) * log (∑ g, p g * z g) := by
  classical
  set μ := ∑ g, p g * z g
  have hμ : 0 ≤ μ := sum_nonneg fun g _ => mul_nonneg (hp.nonneg g) (Nat.cast_nonneg _)
  rcases hμ.eq_or_lt with hμ0 | hμ0
  · -- `μ = 0`: `p` is a point mass at the value `0`.
    rw [← hμ0]
    simp only [zero_add, log_one, mul_zero, zero_mul, sub_zero]
    have hpz : ∀ g, p g ≠ 0 → z g = 0 := fun g hg => by
      have h := (sum_eq_zero_iff_of_nonneg fun g _ =>
        mul_nonneg (hp.nonneg g) (Nat.cast_nonneg (z g))).1 hμ0.symm g (mem_univ g)
      exact_mod_cast (mul_eq_zero.1 h).resolve_left hg
    obtain ⟨g₀, hg₀⟩ : ∃ g, p g ≠ 0 := by
      by_contra h
      push Not at h
      have := hp.sum_eq_one
      simp [h] at this
    have hpt : ∀ g, g ≠ g₀ → p g = 0 := fun g hg => by
      by_contra h
      exact hg (hz ((hpz g h).trans (hpz g₀ hg₀).symm))
    have h1 : p g₀ = 1 := by
      rw [← hp.sum_eq_one, ← add_sum_erase _ _ (mem_univ g₀),
        sum_eq_zero fun g hg => hpt g (ne_of_mem_erase hg), add_zero]
    rw [entropy, ← add_sum_erase _ _ (mem_univ g₀),
      sum_eq_zero fun g hg => by rw [hpt g (ne_of_mem_erase hg), zero_mul], h1]
    simp
  -- The geometric distribution `q(z) = (1/(μ+1)) (μ/(μ+1))^z`.
  set r := μ / (μ + 1)
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [div_lt_one (by linarith)]; linarith
  set q : γ → ℝ := fun g => 1 / (μ + 1) * r ^ z g
  have hq : ∀ g, 0 < q g := fun g => by positivity
  -- `∑ q ≤ 1`, since `z` is injective.
  have hqsum : ∑ g, q g ≤ 1 := by
    set M := (univ.image z).sup id + 1
    have himg : ∑ g, q g = ∑ j ∈ univ.image z, 1 / (μ + 1) * r ^ j :=
      (sum_image (f := fun j => 1 / (μ + 1) * r ^ j) fun a _ b _ h => hz h).symm
    have hsub : univ.image z ⊆ range M := fun j hj =>
      mem_range.2 (Nat.lt_succ_of_le (le_sup (f := id) hj))
    rw [himg]
    calc ∑ j ∈ univ.image z, 1 / (μ + 1) * r ^ j ≤ ∑ j ∈ range M, 1 / (μ + 1) * r ^ j :=
          sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity
      _ = 1 - r ^ M := by
        rw [← mul_sum, geom_sum_eq hr1.ne]
        have : r - 1 = -(1 / (μ + 1)) := by simp only [r]; field_simp; ring
        rw [this]
        field_simp
        ring
      _ ≤ 1 := by linarith [pow_pos hr0 M]
  -- Gibbs' inequality: `H(p) ≤ -∑ p log q`.
  have hgibbs : entropy p ≤ -∑ g, p g * log (q g) := by
    have h : ∑ g, (p g - q g) ≤ ∑ g, p g * log (p g / q g) :=
      sum_le_sum fun g _ => sub_le_mul_log_div (hp.nonneg g) (hq g).le fun h =>
        absurd h (hq g).ne'
    rw [sum_sub_distrib, hp.sum_eq_one] at h
    have e : ∑ g, p g * log (p g / q g) = -entropy p - ∑ g, p g * log (q g) := by
      rw [entropy, neg_neg, ← sum_sub_distrib]
      refine sum_congr rfl fun g _ => ?_
      rcases (hp.nonneg g).eq_or_lt with h0 | h0
      · simp [← h0]
      · rw [log_div h0.ne' (hq g).ne']
        ring
    linarith
  have hval : -∑ g, p g * log (q g) = (μ + 1) * log (μ + 1) - μ * log μ := by
    have hlog : ∀ g, log (q g) = -log (μ + 1) + z g * (log μ - log (μ + 1)) := fun g => by
      have hr : log r = log μ - log (μ + 1) := log_div hμ0.ne' (by positivity)
      have h1 : log (1 / (μ + 1)) = -log (μ + 1) := by rw [one_div, log_inv]
      simp only [q]
      rw [log_mul (by positivity) (by positivity), log_pow, hr, h1]
    simp only [hlog, mul_add, sum_add_distrib, ← sum_mul, hp.sum_eq_one, mul_neg,
      sum_neg_distrib]
    rw [show ∑ g, p g * (z g * (log μ - log (μ + 1))) = μ * (log μ - log (μ + 1)) by
      rw [sum_mul]; exact sum_congr rfl fun g _ => by ring]
    ring
  linarith

/-! ### Markov models of order `k` -/

variable {k : ℕ}

/-- The state after the bit `a`: the last `k` bits, oldest first. -/
def shiftState (s : Fin k → Bool) (a : Bool) : Fin k → Bool :=
  fun i => if h : (i : ℕ) + 1 < k then s ⟨i + 1, h⟩ else a

/-- The state after the string `w`. -/
def advanceState (s : Fin k → Bool) (w : List Bool) : Fin k → Bool := w.foldl shiftState s

lemma advanceState_append (s : Fin k → Bool) (w v : List Bool) :
    advanceState s (w ++ v) = advanceState (advanceState s w) v := by
  simp [advanceState, List.foldl_append]

/-- **(13.98)** The probability `Q_k(w | s) = ∏ⱼ K(wⱼ | wⱼ₋ₖ ⋯ wⱼ₋₁)` of the string `w` under the
`k`-th order Markov kernel `K`, started in the state `s`. -/
def markovProb (K : (Fin k → Bool) → Bool → ℝ) : (Fin k → Bool) → List Bool → ℝ
  | _, [] => 1
  | s, a :: w => K s a * markovProb K (shiftState s a) w

variable {K : (Fin k → Bool) → Bool → ℝ}

lemma markovProb_nonneg (hK : IsChannel K) (s : Fin k → Bool) (w : List Bool) :
    0 ≤ markovProb K s w := by
  induction w generalizing s with
  | nil => simp [markovProb]
  | cons a w ih => exact mul_nonneg ((hK s).nonneg a) (ih _)

lemma markovProb_append (s : Fin k → Bool) (w v : List Bool) :
    markovProb K s (w ++ v) = markovProb K s w * markovProb K (advanceState s w) v := by
  induction w generalizing s with
  | nil => simp [markovProb, advanceState]
  | cons a w ih =>
    rw [List.cons_append, markovProb, markovProb, ih, mul_assoc]
    rfl

/-- The probabilities of the strings of length `l` sum to one. -/
lemma sum_markovProb_ofFn (hK : IsChannel K) (s : Fin k → Bool) (l : ℕ) :
    ∑ w : Fin l → Bool, markovProb K s (List.ofFn w) = 1 := by
  induction l generalizing s with
  | zero => simp [markovProb]
  | succ l ih =>
    rw [sum_cons]
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, markovProb, ← mul_sum, ih, mul_one]
    exact (hK s).sum_eq_one

/-- The state `sᵢ` preceding the `i`-th phrase. -/
def phraseState (s : Fin k → Bool) (ws : List (List Bool)) (i : ℕ) : Fin k → Bool :=
  advanceState s (ws.take i).flatten

/-- **(13.105)–(13.106)** `Q_k(x | s₁) = ∏ᵢ Q_k(yᵢ | sᵢ)` for a parsing `x = y₁ ⋯ y_c`. -/
lemma markovProb_flatten (s : Fin k → Bool) (ws : List (List Bool)) :
    markovProb K s ws.flatten = ∏ i : Fin ws.length, markovProb K (phraseState s ws i) ws[i] := by
  induction ws generalizing s with
  | nil => simp [markovProb]
  | cons w ws ih =>
    rw [List.flatten_cons, markovProb_append, ih]
    refine Eq.trans ?_ (Fin.prod_univ_succ (n := ws.length) _).symm
    congr 1
    refine prod_congr rfl fun i _ => ?_
    simp only [phraseState, Fin.val_succ, List.take_succ_cons, List.flatten_cons,
      advanceState_append, Fin.getElem_fin, List.getElem_cons_succ]

/-! ### Lemma 13.5.5: Ziv's inequality -/

section Ziv

variable (s : Fin k → Bool) (ws : List (List Bool))

lemma length_lt_of_mem_flatten (i : Fin ws.length) :
    ws[i].length < ws.flatten.length + 1 := by
  have : ws[i].length ≤ ws.flatten.length := by
    rw [List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem _))
  omega

/-- The pair `(lᵢ, sᵢ)` of the length of the `i`-th phrase and the state preceding it. -/
def phraseKey (i : Fin ws.length) : Fin (ws.flatten.length + 1) × (Fin k → Bool) :=
  (⟨ws[i].length, length_lt_of_mem_flatten ws i⟩, phraseState s ws i)

/-- The number `c_{ls}` of phrases of length `l` preceded by the state `s` (13.102). -/
def phraseCount (κ : Fin (ws.flatten.length + 1) × (Fin k → Bool)) : ℕ :=
  (univ.filter fun i => phraseKey s ws i = κ).card

lemma sum_phraseCount : ∑ κ, phraseCount s ws κ = ws.length := by
  simp only [phraseCount]
  rw [← card_eq_sum_card_fiberwise (fun i _ => mem_univ (phraseKey s ws i)), card_univ,
    Fintype.card_fin]

/-- **(13.103)** `∑_{l,s} l c_{ls} = n`. -/
lemma sum_phraseCount_mul : ∑ κ, (phraseCount s ws κ : ℝ) * (κ.1 : ℕ) = ws.flatten.length := by
  have h : ∑ κ, (phraseCount s ws κ : ℝ) * (κ.1 : ℕ) =
      ∑ κ, ∑ i ∈ univ.filter (fun i => phraseKey s ws i = κ), (ws[i].length : ℝ) := by
    refine sum_congr rfl fun κ _ => ?_
    rw [phraseCount, sum_congr rfl fun i hi => by
      rw [show (ws[i].length : ℝ) = ((phraseKey s ws i).1 : ℕ) from rfl, (mem_filter.1 hi).2],
      sum_const, nsmul_eq_mul]
  rw [h, sum_fiberwise (g := phraseKey s ws), List.length_flatten, Nat.cast_list_sum,
    List.map_map]
  have := List.sum_ofFn (f := fun i : Fin ws.length => (ws[i].length : ℝ))
  rw [← this]
  congr 1
  apply List.ext_getElem <;> simp

lemma mem_image_ofFn {v : List Bool} {l : ℕ} (h : v.length = l) :
    v ∈ univ.image fun w : Fin l → Bool => List.ofFn w := by
  subst h
  exact mem_image.2 ⟨fun i => v[i], mem_univ _, List.ofFn_getElem⟩

/-- **(13.110)–(13.111)** The distinct phrases of length `l` preceded by the state `σ` have total
probability at most one. -/
lemma sum_fiber_markovProb_le (hK : IsChannel K) (hnd : ws.Nodup)
    (κ : Fin (ws.flatten.length + 1) × (Fin k → Bool)) :
    ∑ i ∈ univ.filter (fun i => phraseKey s ws i = κ),
      markovProb K (phraseState s ws i) ws[i] ≤ 1 := by
  set G := univ.filter (fun i => phraseKey s ws i = κ)
  have hkey : ∀ i ∈ G, phraseKey s ws i = κ := fun i hi => (mem_filter.1 hi).2
  have hstate : ∀ i ∈ G, phraseState s ws i = κ.2 := fun i hi => by
    rw [← hkey i hi]; rfl
  have hlen : ∀ i ∈ G, ws[i].length = (κ.1 : ℕ) := fun i hi => by
    rw [← hkey i hi]; rfl
  rw [sum_congr rfl fun i hi => by rw [hstate i hi]]
  have hinj : Set.InjOn (fun i : Fin ws.length => ws[i]) G := fun i _ j _ h =>
    Fin.ext ((hnd.getElem_inj_iff).1 h)
  rw [← sum_image (f := markovProb K κ.2) hinj]
  have hsub : G.image (fun i : Fin ws.length => ws[i]) ⊆
      univ.image fun w : Fin (κ.1 : ℕ) → Bool => List.ofFn w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hv
    exact mem_image_ofFn (hlen i hi)
  refine (sum_le_sum_of_subset_of_nonneg hsub fun v _ _ => markovProb_nonneg hK _ _).trans ?_
  rw [sum_image fun a _ b _ h => List.ofFn_injective h, sum_markovProb_ofFn hK]

/-- `∑ᵢ log aᵢ ≤ m log (∑ᵢ aᵢ / m)` for `m` positive numbers. -/
lemma sum_log_le {ι : Type*} (G : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ G, 0 < a i)
    (hG : G.Nonempty) : ∑ i ∈ G, log (a i) ≤ G.card * log ((∑ i ∈ G, a i) / G.card) := by
  set S := ∑ i ∈ G, a i
  set m : ℝ := (G.card : ℝ)
  have hm : 0 < m := by simp only [m]; exact_mod_cast hG.card_pos
  have hS : 0 < S := sum_pos ha hG
  have h : ∀ i ∈ G, log (a i) ≤ log (S / m) + (a i * m / S - 1) := fun i hi => by
    have := log_le_sub_one_of_pos (show 0 < a i * m / S by have := ha i hi; positivity)
    rw [show a i * m / S = a i / (S / m) by field_simp,
      log_div (ha i hi).ne' (by positivity)] at this
    rw [show a i * m / S = a i / (S / m) by field_simp]
    linarith
  refine (sum_le_sum h).trans (le_of_eq ?_)
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, sum_sub_distrib, sum_const, nsmul_eq_mul,
    ← sum_div, ← sum_mul]
  field_simp
  ring

/-- **Lemma 13.5.5 (Ziv's inequality), (13.104)–(13.111).** For a distinct parsing of `x` and every
`k`-th order Markov model, `log Q_k(x | s₁) ≤ -∑_{l,s} c_{ls} log c_{ls}`. -/
theorem log_markovProb_le (hK : IsChannel K) (hnd : ws.Nodup)
    (hQ : 0 < markovProb K s ws.flatten) :
    log (markovProb K s ws.flatten) ≤
      -∑ κ, (phraseCount s ws κ : ℝ) * log (phraseCount s ws κ) := by
  set f := fun i : Fin ws.length => markovProb K (phraseState s ws i) ws[i]
  have hQf := markovProb_flatten (K := K) s ws
  have hf : ∀ i, 0 < f i := fun i => by
    refine lt_of_le_of_ne (markovProb_nonneg hK _ _) fun h => ?_
    rw [hQf, prod_eq_zero (mem_univ i) h.symm] at hQ
    exact lt_irrefl _ hQ
  rw [hQf, log_prod fun i _ => (hf i).ne', ← sum_fiberwise (g := phraseKey s ws), ←
    sum_neg_distrib]
  refine sum_le_sum fun κ _ => ?_
  set G := univ.filter (fun i => phraseKey s ws i = κ)
  rcases G.eq_empty_or_nonempty with hG | hG
  · simp [phraseCount, G, hG]
  have h1 := sum_log_le G f (fun i _ => hf i) hG
  have hS := sum_fiber_markovProb_le s ws hK hnd κ
  have hSpos : 0 < ∑ i ∈ G, f i := sum_pos (fun i _ => hf i) hG
  have hm : (0 : ℝ) < G.card := by exact_mod_cast hG.card_pos
  have h2 : log ((∑ i ∈ G, f i) / G.card) ≤ log (1 / G.card) :=
    log_le_log (by positivity) (div_le_div_of_nonneg_right hS hm.le)
  rw [one_div, log_inv] at h2
  change ∑ i ∈ G, log (f i) ≤ -((G.card : ℝ) * log G.card)
  nlinarith

end Ziv

/-! ### Theorem 13.5.2: the number of phrases -/

lemma markovProb_le_one (hK : IsChannel K) (s : Fin k → Bool) (w : List Bool) :
    markovProb K s w ≤ 1 := by
  induction w generalizing s with
  | nil => simp [markovProb]
  | cons a w ih =>
    rw [markovProb]
    calc K s a * markovProb K (shiftState s a) w ≤ 1 * 1 :=
          mul_le_mul ((hK s).le_one a) (ih _) (markovProb_nonneg hK _ _) zero_le_one
      _ = 1 := one_mul 1

lemma length_le_flatten_length {ws : List (List Bool)} (hne : ∀ w ∈ ws, w ≠ []) :
    ws.length ≤ ws.flatten.length := by
  rw [List.length_flatten]
  have : ∀ w ∈ ws, 1 ≤ w.length := fun w hw => List.length_pos_iff.2 (hne w hw)
  have h := List.length_le_sum_of_one_le (ws.map List.length) (by simpa using this)
  rwa [List.length_map] at h

/-- `(μ + 1) log (μ + 1) - μ log μ ≤ log μ + 1 + 1/μ`. -/
lemma geom_entropy_le {μ : ℝ} (hμ : 0 < μ) :
    (μ + 1) * log (μ + 1) - μ * log μ ≤ log μ + 1 + 1 / μ := by
  have h1 : log (μ + 1) = log μ + log (1 + 1 / μ) := by
    rw [← log_mul hμ.ne' (by positivity)]
    congr 1
    field_simp
  have h2 : log (1 + 1 / μ) ≤ 1 / μ := by
    have := log_le_sub_one_of_pos (show 0 < 1 + 1 / μ by positivity)
    linarith
  rw [h1]
  have : (μ + 1) * log (1 + 1 / μ) ≤ (μ + 1) * (1 / μ) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  have e : (μ + 1) * (1 / μ) = 1 + 1 / μ := by field_simp
  nlinarith

/-- **(13.113)–(13.123)** For a distinct parsing of `x` into `c` nonempty phrases and every
`k`-th order Markov model, `c log c ≤ -log Q_k(x | s₁) + c (k log 2 + log (n/c) + 1 + c/n)`. -/
theorem length_mul_log_length_le (hK : IsChannel K) (s : Fin k → Bool) {ws : List (List Bool)}
    (hnd : ws.Nodup) (hne : ∀ w ∈ ws, w ≠ []) (hc : ws ≠ [])
    (hQ : 0 < markovProb K s ws.flatten) :
    (ws.length : ℝ) * log ws.length ≤ -log (markovProb K s ws.flatten) +
      ws.length * (k * log 2 + log (ws.flatten.length / ws.length) + 1 +
        ws.length / ws.flatten.length) := by
  classical
  set c : ℝ := (ws.length : ℝ)
  set n : ℝ := (ws.flatten.length : ℝ)
  have hc0 : 0 < c := by
    have := List.length_pos_iff.2 hc
    simp only [c]
    exact_mod_cast this
  -- `n ≥ c`, since the phrases are nonempty.
  have hnc : c ≤ n := by
    simp only [c, n]
    exact_mod_cast length_le_flatten_length hne
  have hn0 : 0 < n := lt_of_lt_of_le hc0 hnc
  set pr : Fin (ws.flatten.length + 1) × (Fin k → Bool) → ℝ := fun κ => phraseCount s ws κ / c
  have hcsum : ∑ κ, (phraseCount s ws κ : ℝ) = c := by
    simp only [c]
    exact_mod_cast sum_phraseCount s ws
  have hpr : IsPMF pr := by
    refine ⟨fun κ => by positivity, ?_⟩
    simp only [pr, ← sum_div]
    rw [hcsum]
    exact div_self hc0.ne'
  -- `∑ c_{ls} log c_{ls} = c log c - c H(pr)`.
  have hident : ∑ κ, (phraseCount s ws κ : ℝ) * log (phraseCount s ws κ) =
      c * log c - c * entropy pr := by
    rw [entropy, mul_neg, sub_neg_eq_add, mul_sum]
    have hsum : c * log c = ∑ κ, (phraseCount s ws κ : ℝ) * log c := by
      rw [← sum_mul, hcsum]
    rw [hsum, ← sum_add_distrib]
    refine sum_congr rfl fun κ _ => ?_
    simp only [pr]
    rcases Nat.eq_zero_or_pos (phraseCount s ws κ) with h0 | h0
    · simp [h0]
    have : (0 : ℝ) < phraseCount s ws κ := by exact_mod_cast h0
    rw [log_div this.ne' hc0.ne']
    field_simp
    ring
  -- `H(pr) ≤ H(U) + H(V)`.
  have hsub : entropy pr ≤ entropy (dist pr Prod.fst) + entropy (dist pr Prod.snd) := by
    have h := chain_rule hpr Prod.fst Prod.snd
    have h2 := condEntropy_le_entropy hpr (Prod.snd : _ → Fin k → Bool) Prod.fst
    have h3 : H[pair Prod.fst Prod.snd ; pr] = entropy pr := by
      rw [entropyRV, dist_pair_fst_snd]
    simp only [entropyRV] at h h2 h3
    linarith
  have hV : entropy (dist pr Prod.snd) ≤ k * log 2 := by
    have := entropy_le_log_card (hpr.dist (Prod.snd : _ → Fin k → Bool))
    simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, log_pow]
      using this
  -- The mean phrase length is `n/c`.
  have hmean : ∑ l : Fin (ws.flatten.length + 1), dist pr Prod.fst l * ((l : ℕ) : ℝ) = n / c := by
    simp only [dist, sum_mul, ite_mul, zero_mul]
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, ite_true]
    simp only [pr, div_mul_eq_mul_div, ← sum_div, sum_phraseCount_mul]
    rfl
  have hU := entropy_le_of_mean (hpr.dist (Prod.fst : _ → Fin (ws.flatten.length + 1)))
    (z := fun l => (l : ℕ)) Fin.val_injective
  rw [hmean] at hU
  have hU' := geom_entropy_le (show 0 < n / c by positivity)
  have hZiv := log_markovProb_le s ws hK hnd hQ
  rw [hident] at hZiv
  have hH : entropy pr ≤ k * log 2 + log (n / c) + 1 + c / n := by
    have : 1 / (n / c) = c / n := by field_simp
    rw [this] at hU'
    linarith
  have := mul_le_mul_of_nonneg_left hH hc0.le
  linarith

/-- `t log (1/t) ≤ 2 √t` for `t > 0`. -/
lemma mul_log_inv_le_two_sqrt {t : ℝ} (ht : 0 < t) : t * log (1 / t) ≤ 2 * √t := by
  have hs : 0 < √t := Real.sqrt_pos.2 ht
  have h := log_le_sub_one_of_pos (show 0 < 1 / √t by positivity)
  have e : log (1 / t) = 2 * log (1 / √t) := by
    rw [← log_rpow (by positivity), show (1 / √t) ^ (2 : ℝ) = 1 / t by
      rw [rpow_two, div_pow, one_pow, Real.sq_sqrt ht.le]]
  rw [e]
  have : t * (2 * log (1 / √t)) ≤ t * (2 * (1 / √t - 1)) :=
    mul_le_mul_of_nonneg_left (by linarith) ht.le
  have e2 : t * (2 * (1 / √t - 1)) = 2 * √t - 2 * t := by
    have h' : t / √t = √t := Real.div_sqrt
    calc t * (2 * (1 / √t - 1)) = 2 * (t / √t) - 2 * t := by ring
      _ = 2 * √t - 2 * t := by rw [h']
  linarith

/-- **(13.124)–(13.125)** Uniformly over all strings of length `n` with a distinct parsing into
nonempty phrases and over all `k`-th order Markov models,
`c log c ≤ -log Q_k(x | s₁) + ε n` for `n` large enough. -/
theorem exists_length_mul_log_length_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ ws : List (List Bool), ws.Nodup → (∀ w ∈ ws, w ≠ []) → N ≤ ws.flatten.length →
      ∀ (K : (Fin k → Bool) → Bool → ℝ), IsChannel K → ∀ s : Fin k → Bool,
        0 < markovProb K s ws.flatten →
        (ws.length : ℝ) * log ws.length ≤ -log (markovProb K s ws.flatten) +
          ε * ws.flatten.length := by
  set A := (k : ℝ) * log 2 + 2
  have hA : 0 < A := by have := log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  set δ := min (ε / (2 * A)) (ε ^ 2 / 16)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := exists_length_le_mul_of_nodup hδ
  refine ⟨max N 1, fun ws hnd hne hn K hK s hQ => ?_⟩
  have hc := hN ws hnd ((le_max_left _ _).trans hn)
  have hws : ws ≠ [] := by
    rintro rfl
    simp at hn
  set c : ℝ := (ws.length : ℝ)
  set n : ℝ := (ws.flatten.length : ℝ)
  have hc0 : 0 < c := by
    have := List.length_pos_iff.2 hws
    simp only [c]
    exact_mod_cast this
  have hn0 : 0 < n := by
    simp only [n]
    exact_mod_cast (lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hn))
  have hmain := length_mul_log_length_le hK s hnd hne hws hQ
  have hcn : c / n ≤ 1 := by
    rw [div_le_one hn0]
    simp only [c, n]
    exact_mod_cast length_le_flatten_length hne
  -- The first error term: `c (k log 2 + 1 + c/n) ≤ c A ≤ δ A n ≤ ε n / 2`.
  have h1 : c * ((k : ℝ) * log 2 + 1 + c / n) ≤ ε / 2 * n := by
    have : c * ((k : ℝ) * log 2 + 1 + c / n) ≤ c * A :=
      mul_le_mul_of_nonneg_left (by simp only [A]; linarith) hc0.le
    have h2 : c * A ≤ δ * n * A := mul_le_mul_of_nonneg_right hc hA.le
    have h3 : δ * A ≤ ε / 2 := by
      have := min_le_left (ε / (2 * A)) (ε ^ 2 / 16)
      calc δ * A ≤ ε / (2 * A) * A := mul_le_mul_of_nonneg_right this hA.le
        _ = ε / 2 := by field_simp
    nlinarith
  -- The second error term: `c log (n/c) = n t log (1/t) ≤ 2 n √t ≤ ε n / 2`, `t = c/n ≤ δ`.
  have h2 : c * log (n / c) ≤ ε / 2 * n := by
    set t := c / n
    have ht : 0 < t := by positivity
    have htδ : t ≤ δ := by rw [div_le_iff₀ hn0]; exact hc
    have e : c * log (n / c) = n * (t * log (1 / t)) := by
      simp only [t, one_div_div]
      field_simp
    rw [e]
    have hsq : 2 * √t ≤ ε / 2 := by
      have : √t ≤ √(ε ^ 2 / 16) := Real.sqrt_le_sqrt (htδ.trans (min_le_right _ _))
      rw [show ε ^ 2 / 16 = (ε / 4) ^ 2 by ring, Real.sqrt_sq (by positivity)] at this
      linarith
    have := mul_log_inv_le_two_sqrt ht
    nlinarith
  nlinarith

/-- **Theorem 13.5.2, (13.112), (13.126).** Let `x₁ x₂ ⋯` be a binary sequence, and for each `n`
let a distinct parsing of `x₁ ⋯ xₙ` into `c(n)` nonempty phrases be given. If, for a `k`-th order
Markov model, `-(1/n) log Q_k(x₁ ⋯ xₙ | s₁) → h`, then `lim sup c(n) log c(n) / n ≤ h`. For an
ergodic source, the ergodic theorem gives `h = H(X₀ | X₋₁, …, X₋ₖ)` with probability one. -/
theorem eventually_length_mul_log_length_le {x : ℕ → Bool} {parse : ℕ → List (List Bool)}
    (hparse : ∀ n, (parse n).flatten = List.ofFn fun i : Fin n => x i)
    (hnd : ∀ n, (parse n).Nodup) (hne : ∀ n, ∀ w ∈ parse n, w ≠ [])
    (hK : IsChannel K) (s : Fin k → Bool)
    (hQ : ∀ n, 0 < markovProb K s (List.ofFn fun i : Fin n => x i)) {h : ℝ}
    (hlim : Tendsto (fun n : ℕ => -log (markovProb K s (List.ofFn fun i : Fin n => x i)) / n)
      atTop (𝓝 h)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ((parse n).length : ℝ) * log (parse n).length / n ≤ h + ε := by
  obtain ⟨N, hN⟩ := exists_length_mul_log_length_le k (half_pos hε)
  filter_upwards [(tendsto_order.1 hlim).2 _ (show h < h + ε / 2 by linarith),
    eventually_ge_atTop (max N 1)] with n hn hnN
  have hlen : (parse n).flatten.length = n := by rw [hparse]; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_of_max_le_right hnN)
  have h1 := hN (parse n) (hnd n) (hne n) (by rw [hlen]; exact le_of_max_le_left hnN) K hK s
    (by rw [hparse]; exact hQ n)
  rw [hparse, List.length_ofFn] at h1
  rw [div_le_iff₀ hn0]
  rw [div_lt_iff₀ hn0] at hn
  linarith

/-! ### Theorem 13.5.3: the LZ78 code -/

lemma ne_nil_of_prefixClosed {D ws : List (List Bool)} (h : PrefixClosed D ws) :
    ∀ w ∈ ws, w ≠ [] := by
  induction ws generalizing D with
  | nil => simp
  | cons v ws ih =>
    obtain ⟨hv, -, hrest⟩ := h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact hv
    · exact ih hrest w hw

/-- `⌈log₂ c⌉ log 2 ≤ log c + log 2`. -/
lemma clog_mul_log_two_le (c : ℕ) : (Nat.clog 2 c : ℝ) * log 2 ≤ log c + log 2 := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  rcases Nat.lt_or_ge 1 c with hc | hc
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hc
    have h' : ((2 : ℝ) ^ (Nat.clog 2 c).pred) < c := by exact_mod_cast h
    have := log_lt_log (by positivity) h'
    rw [log_pow] at this
    have hpos : 0 < Nat.clog 2 c := Nat.clog_pos (by norm_num) hc
    have e : ((Nat.clog 2 c).pred : ℝ) = Nat.clog 2 c - 1 := by
      rw [Nat.pred_eq_sub_one, Nat.cast_sub hpos]
      simp
    rw [e] at this
    linarith
  · rw [Nat.clog_of_right_le_one hc]
    have : 0 ≤ log (c : ℝ) := by
      rcases Nat.lt_or_ge c 1 with h | h
      · simp [Nat.lt_one_iff.1 h]
      · exact log_nonneg (by exact_mod_cast h)
    simp only [Nat.cast_zero, zero_mul]
    linarith

/-- `(c + 1) log (c + 1) ≤ c log c + log (c + 1) + 1`. -/
lemma succ_mul_log_succ_le {c : ℝ} (hc : 0 ≤ c) :
    (c + 1) * log (c + 1) ≤ c * log c + log (c + 1) + 1 := by
  rcases hc.eq_or_lt with h0 | h0
  · simp [← h0]
  have h1 : log (c + 1) - log c ≤ 1 / c := by
    rw [← log_div (by positivity) h0.ne']
    have := log_le_sub_one_of_pos (show 0 < (c + 1) / c by positivity)
    have e : (c + 1) / c - 1 = 1 / c := by field_simp; ring
    linarith
  have := mul_le_mul_of_nonneg_left h1 h0.le
  rw [mul_one_div_cancel h0.ne'] at this
  nlinarith

/-- **Theorem 13.5.3, (13.129)–(13.130).** Uniformly over all binary strings `x` of length `n` and
all `k`-th order Markov models, the LZ78 code length satisfies
`l(x) log 2 ≤ -log Q_k(x | s₁) + ε n` for `n` large enough. -/
theorem exists_lz78Length_le (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ x : List Bool, N ≤ x.length →
      ∀ (K : (Fin k → Bool) → Bool → ℝ), IsChannel K → ∀ s : Fin k → Bool,
        0 < markovProb K s x →
        (lz78Length x : ℝ) * log 2 ≤ -log (markovProb K s x) + ε * x.length := by
  have hl : 0 < log 2 := log_pos (by norm_num)
  obtain ⟨N₁', hN₁⟩ := exists_length_mul_log_length_le k (show 0 < ε / 4 by positivity)
  set N₁ := max N₁' 1
  obtain ⟨N₂, hN₂⟩ := exists_length_le_mul_of_nodup (show 0 < ε / (8 * log 2) by positivity)
  set C : ℝ := N₁ * log N₁ + 2 * log 2 * (N₂ + 1) + 1
  have hsmall : ∀ᶠ n : ℕ in atTop, log ((n : ℝ) + 1) + C ≤ ε / 2 * n := by
    have h := tendsto_log_add_one_div.add (tendsto_const_div_atTop_nhds_zero_nat C)
    rw [add_zero] at h
    filter_upwards [(tendsto_order.1 h).2 _ (show (0 : ℝ) < ε / 2 by positivity),
      eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [← add_div, div_lt_iff₀ hn'] at hn
    linarith
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 hsmall
  refine ⟨N₃, fun x hx K hK s hQ => ?_⟩
  set ws := (lz78Parse x).1
  have hxe : ws.flatten ++ (lz78Parse x).2 = x := lz78Parse_flatten x
  have hnd : ws.Nodup := lz78Parse_nodup x
  have hne : ∀ w ∈ ws, w ≠ [] := ne_nil_of_prefixClosed (lz78Parse_prefixClosed x)
  set c' : ℝ := (ws.length : ℝ)
  set n : ℝ := (x.length : ℝ)
  have hc'0 : 0 ≤ c' := Nat.cast_nonneg _
  have hn'le : ws.flatten.length ≤ x.length := by
    rw [← hxe, List.length_append]
    exact Nat.le_add_right _ _
  have hc'n' : ws.length ≤ ws.flatten.length := length_le_flatten_length hne
  have hc'n : c' ≤ n := by
    simp only [c', n]
    exact_mod_cast hc'n'.trans hn'le
  -- `Q(x) ≤ Q(y₁ ⋯ y_c)`.
  have hQx : markovProb K s x ≤ markovProb K s ws.flatten := by
    rw [← hxe, markovProb_append]
    exact mul_le_of_le_one_right (markovProb_nonneg hK _ _) (markovProb_le_one hK _ _)
  have hQ' : 0 < markovProb K s ws.flatten := hQ.trans_le hQx
  have hlogQ : -log (markovProb K s ws.flatten) ≤ -log (markovProb K s x) :=
    neg_le_neg (log_le_log hQ hQx)
  have hlogQ0 : 0 ≤ -log (markovProb K s ws.flatten) := by
    have := log_nonpos hQ'.le (markovProb_le_one hK s ws.flatten)
    linarith
  have hN₁0 : 0 ≤ (N₁ : ℝ) * log N₁ := by
    have : (1 : ℝ) ≤ N₁ := by exact_mod_cast le_max_right N₁' 1
    exact mul_nonneg (by linarith) (log_nonneg this)
  -- `c' log c' ≤ -log Q(x) + ε n / 4 + N₁ log N₁`.
  have hA : c' * log c' ≤ -log (markovProb K s x) + ε / 4 * n + N₁ * log N₁ := by
    by_cases hN : N₁' ≤ ws.flatten.length
    · have h : c' * log c' ≤ -log (markovProb K s ws.flatten) + ε / 4 * ws.flatten.length :=
        hN₁ ws hnd hne hN K hK s hQ'
      have : ε / 4 * ws.flatten.length ≤ ε / 4 * n :=
        mul_le_mul_of_nonneg_left (by simp only [n]; exact_mod_cast hn'le) (by positivity)
      linarith
    · push Not at hN
      have hc'N : c' ≤ N₁ := by
        simp only [c', N₁]
        exact_mod_cast (hc'n'.trans hN.le).trans (le_max_left _ _)
      have h2 : c' * log c' ≤ N₁ * log N₁ := by
        rcases hc'0.eq_or_lt with h0 | h0
        · rw [← h0]
          simpa using hN₁0
        · have h1 : (1 : ℝ) ≤ c' := by
            have : ws ≠ [] := fun h => by simp [c', h] at h0
            simp only [c']
            exact_mod_cast List.length_pos_iff.2 this
          exact mul_le_mul hc'N (log_le_log h0 hc'N) (log_nonneg h1) (by linarith)
      have : 0 ≤ ε / 4 * n := by positivity
      linarith
  -- `c' ≤ ε n / (8 log 2) + N₂`.
  have hB : c' ≤ ε / (8 * log 2) * n + N₂ := by
    by_cases hN : N₂ ≤ ws.flatten.length
    · have h : c' ≤ ε / (8 * log 2) * ws.flatten.length := hN₂ ws hnd hN
      have : ε / (8 * log 2) * ws.flatten.length ≤ ε / (8 * log 2) * n :=
        mul_le_mul_of_nonneg_left (by simp only [n]; exact_mod_cast hn'le) (by positivity)
      have : (0 : ℝ) ≤ N₂ := Nat.cast_nonneg _
      linarith
    · push Not at hN
      have : c' ≤ N₂ := by simp only [c']; exact_mod_cast hc'n'.trans hN.le
      have : 0 ≤ ε / (8 * log 2) * n := by positivity
      linarith
  -- The LZ78 code length.
  set c : ℕ := lz78Count x
  have hcc : (c : ℝ) = c' ∨ (c : ℝ) = c' + 1 := by
    simp only [c, c', lz78Count]
    split_ifs
    · left; simp [ws]
    · right; push_cast; simp [ws]
  have hlen : (lz78Length x : ℝ) * log 2 ≤ c * log c + 2 * c * log 2 := by
    rw [lz78Length]
    push_cast
    have := clog_mul_log_two_le c
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    nlinarith
  have hclog : (c : ℝ) * log c ≤ c' * log c' + log (c' + 1) + 1 := by
    rcases hcc with h | h
    · rw [h]
      have : 0 ≤ log (c' + 1) := log_nonneg (by linarith)
      linarith
    · rw [h]
      exact succ_mul_log_succ_le hc'0
  have hc1 : (c : ℝ) ≤ c' + 1 := by rcases hcc with h | h <;> linarith
  have hlogn : log (c' + 1) ≤ log (n + 1) := log_le_log (by linarith) (by linarith)
  have hsm := hN₃ x.length hx
  have e : 2 * log 2 * (ε / (8 * log 2) * n) = ε / 4 * n := by field_simp; ring
  have h2c : 2 * (c : ℝ) * log 2 ≤ 2 * log 2 * (ε / (8 * log 2) * n) + 2 * log 2 * (N₂ + 1) := by
    nlinarith
  simp only [C] at hsm
  linarith

/-- **Theorem 13.5.3 (for a sequence).** If `-(1/n) log Q_k(x₁ ⋯ xₙ | s₁) → h`, then the LZ78 code
length satisfies `lim sup l(x₁ ⋯ xₙ) log 2 / n ≤ h`. For an ergodic source, `h` is the entropy of
the `k`-th order Markov approximation, which tends to the entropy rate as `k → ∞`. -/
theorem eventually_lz78Length_le {x : ℕ → Bool} (hK : IsChannel K) (s : Fin k → Bool)
    (hQ : ∀ n, 0 < markovProb K s (List.ofFn fun i : Fin n => x i)) {h : ℝ}
    (hlim : Tendsto (fun n : ℕ => -log (markovProb K s (List.ofFn fun i : Fin n => x i)) / n)
      atTop (𝓝 h)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (lz78Length (List.ofFn fun i : Fin n => x i) : ℝ) * log 2 / n ≤ h + ε := by
  obtain ⟨N, hN⟩ := exists_lz78Length_le k (half_pos hε)
  filter_upwards [(tendsto_order.1 hlim).2 _ (show h < h + ε / 2 by linarith),
    eventually_ge_atTop (max N 1)] with n hn hnN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le zero_lt_one (le_of_max_le_right hnN)
  have h1 := hN (List.ofFn fun i : Fin n => x i) (by simpa using le_of_max_le_left hnN) K hK s
    (hQ n)
  rw [List.length_ofFn] at h1
  rw [div_le_iff₀ hn0]
  rw [div_lt_iff₀ hn0] at hn
  linarith

end InfoTheory
