/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Entropy.Bounds
public import InfoTheoryLib.RelativeEntropy.Pinsker
public import InfoTheoryLib.Statistics.Types
public import InfoTheoryLib.Probability.IID

/-!
# Bounds on entropy and relative entropy

Three inequalities of Sections 17.1 and 17.3. The entropy is continuous in the `L₁` distance:
`|H(p) - H(q)| ≤ -‖p - q‖₁ log (‖p - q‖₁ / |𝒳|)` when `‖p - q‖₁ ≤ 1/2` (Theorem 17.3.3). Near
`Q`, the relative entropy is half the `χ²` distance, `D(P ‖ Q) = χ²(P, Q)/2 + O(‖P - Q‖³)`
(Lemma 17.3.3). And the expected relative entropy `E D(p̂ₙ ‖ p)` of the empirical distribution
of `n` i.i.d. samples decreases with `n` (Theorem 17.1.11).

## Main definitions

* `chiSq P Q`: the `χ²` distance `∑ₓ (P(x) - Q(x))²/Q(x)`.

## Main statements

* `abs_negMulLog_sub_le`: `|η(t) - η(t + ν)| ≤ η(ν)` for `η(t) = -t log t` and `ν ≤ 1/2`,
  (17.27).
* `abs_entropy_sub_le`: **Theorem 17.3.3 (L₁ bound on entropy)**.
* `abs_relEntropyReal_sub_chiSq_le`, `tendsto_relEntropyReal_div_sq`: **Lemma 17.3.3**,
  `D(Q + tΔ ‖ Q) = χ²(Q + tΔ, Q)/2 + O(t³)`.
* `typeOf_eq_sum_removeNth`: the type of `n + 1` symbols is the average of the types of its
  leave-one-out subsequences.
* `expect_relEntropy_typeOf_succ_le`: **Theorem 17.1.11**, `E D(p̂ₙ ‖ p) ≤ E D(p̂ₙ₋₁ ‖ p)`.

## Implementation notes

Logarithms are natural. Lemma 17.3.3 is stated along a line `P = Q + tΔ` with `∑ Δ = 0` and
`Q > 0`, with the explicit error bound `4|t|³ ∑ |Δ|³/Q²`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 17.1
  and 17.3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-! ### The `L₁` bound on entropy -/

/-- `η(t) = -t log t` is subadditive. -/
lemma negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negMulLog (a + b) ≤ negMulLog a + negMulLog b := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  rcases hb.eq_or_lt with rfl | hb'
  · simp
  have h1 := mul_le_mul_of_nonneg_left (log_le_log ha' (by linarith : a ≤ a + b)) ha
  have h2 := mul_le_mul_of_nonneg_left (log_le_log hb' (by linarith : b ≤ a + b)) hb
  simp only [negMulLog]
  linarith

/-- For a concave `f`, `f(a) + f(b) ≤ f(x) + f(y)` when `a ≤ x ≤ b` and `x + y = a + b`. -/
lemma ConcaveOn.add_le_add_of_le {f : ℝ → ℝ} {s : Set ℝ} (hf : ConcaveOn ℝ s f) {a b x y : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hax : a ≤ x) (hxb : x ≤ b) (hxy : x + y = a + b) :
    f a + f b ≤ f x + f y := by
  rcases hax.eq_or_lt with rfl | hax'
  · rw [show y = b by linarith]
  have hab : 0 < b - a := by linarith
  set l := (b - x) / (b - a)
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hab.le
  have hl1 : 0 ≤ 1 - l := by
    rw [sub_nonneg, div_le_one hab]; linarith
  have hx : l • a + (1 - l) • b = x := by
    simp only [smul_eq_mul, l]; field_simp; ring
  have hy : (1 - l) • a + l • b = y := by
    rw [show y = a + b - x by linarith]
    simp only [smul_eq_mul, l]; field_simp; ring
  have h1 := hf.2 ha hb hl0 hl1 (by ring)
  have h2 := hf.2 ha hb hl1 hl0 (by ring)
  rw [hx] at h1
  rw [hy] at h2
  simp only [smul_eq_mul] at h1 h2
  linarith

/-- `η(1 - ν) ≤ η(ν)` for `0 ≤ ν ≤ 1/2`. -/
lemma negMulLog_one_sub_le {ν : ℝ} (hν : 0 ≤ ν) (hν2 : ν ≤ 1 / 2) :
    negMulLog (1 - ν) ≤ negMulLog ν := by
  rcases hν.eq_or_lt with rfl | hν0
  · simp
  have h1ν : 0 < 1 - ν := by linarith
  have ha : (1 - 2 * ν) / (1 - ν) ≤ log (1 - ν) - log ν := by
    rw [← log_div h1ν.ne' hν0.ne']
    refine le_trans (le_of_eq ?_) (one_sub_inv_le_log_of_pos (div_pos h1ν hν0))
    field_simp
    ring
  have hb : -ν / (1 - ν) ≤ log (1 - ν) := by
    refine le_trans (le_of_eq ?_) (one_sub_inv_le_log_of_pos h1ν)
    field_simp
    ring
  have e1 := mul_le_mul_of_nonneg_left ha hν
  have e2 := mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 1 - 2 * ν)
  have e3 : ν * ((1 - 2 * ν) / (1 - ν)) + (1 - 2 * ν) * (-ν / (1 - ν)) = 0 := by
    field_simp
    ring
  simp only [negMulLog]
  nlinarith

/-- **(17.27)** For `0 ≤ ν ≤ 1/2` and `0 ≤ t ≤ 1 - ν`, `|η(t) - η(t + ν)| ≤ η(ν)`, where
`η(t) = -t log t`. -/
lemma abs_negMulLog_sub_le {t ν : ℝ} (ht : 0 ≤ t) (hν : 0 ≤ ν) (hν2 : ν ≤ 1 / 2)
    (htν : t + ν ≤ 1) : |negMulLog t - negMulLog (t + ν)| ≤ negMulLog ν := by
  rw [abs_le]
  refine ⟨by linarith [negMulLog_add_le ht hν], ?_⟩
  have h := ConcaveOn.add_le_add_of_le concaveOn_negMulLog (a := t) (b := 1) (x := t + ν)
    (y := 1 - ν) (Set.mem_Ici.2 ht) (Set.mem_Ici.2 zero_le_one) (by linarith) htν (by ring)
  rw [negMulLog_one] at h
  linarith [negMulLog_one_sub_le hν hν2]

/-- `∑ₓ η(r(x)) ≤ -L log (L / |𝒳|)` for `r ≥ 0` with `∑ₓ r(x) = L`, (17.31)–(17.33). -/
lemma sum_negMulLog_le {r : α → ℝ} (hr : ∀ x, 0 ≤ r x) :
    ∑ x, negMulLog (r x) ≤ -(∑ x, r x) * log ((∑ x, r x) / Fintype.card α) := by
  set L := ∑ x, r x
  rcases (sum_nonneg fun x _ => hr x : 0 ≤ L).eq_or_lt with hL | hL
  · have h0 : ∀ x, r x = 0 := fun x =>
      (sum_eq_zero_iff_of_nonneg fun x _ => hr x).1 hL.symm x (mem_univ x)
    rw [show L = 0 from hL.symm]
    simp [h0]
  have hpmf : IsPMF fun x => r x / L :=
    ⟨fun x => div_nonneg (hr x) hL.le, by rw [← sum_div, div_self hL.ne']⟩
  have hcard : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hpmf
  have hH := entropy_le_log_card hpmf
  rw [entropy_eq_sum_negMulLog] at hH
  have e : ∀ x, negMulLog (r x) = r x / L * negMulLog L + L * negMulLog (r x / L) := by
    intro x
    rw [← negMulLog_mul, mul_div_cancel₀ _ hL.ne']
  calc ∑ x, negMulLog (r x)
      = (∑ x, r x / L) * negMulLog L + L * ∑ x, negMulLog (r x / L) := by
        simp only [e, sum_add_distrib, ← sum_mul, ← mul_sum]
    _ ≤ 1 * negMulLog L + L * log (Fintype.card α) := by
        rw [← sum_div, div_self hL.ne']
        gcongr
    _ = -L * log (L / Fintype.card α) := by
        rw [log_div hL.ne' hcard.ne', negMulLog]
        ring

/-- **Theorem 17.3.3 (L₁ bound on entropy), (17.25)–(17.33).** If `‖p - q‖₁ ≤ 1/2`, then
`|H(p) - H(q)| ≤ -‖p - q‖₁ log (‖p - q‖₁ / |𝒳|)`. -/
theorem abs_entropy_sub_le {p q : α → ℝ} (hp : IsPMF p) (hq : IsPMF q) (h : l1Dist p q ≤ 1 / 2) :
    |entropy p - entropy q| ≤ -l1Dist p q * log (l1Dist p q / Fintype.card α) := by
  have hr : ∀ x, |negMulLog (p x) - negMulLog (q x)| ≤ negMulLog |p x - q x| := by
    intro x
    have hx : |p x - q x| ≤ 1 / 2 :=
      (single_le_sum (fun y _ => abs_nonneg (p y - q y)) (mem_univ x)).trans h
    rcases le_total (p x) (q x) with hle | hle
    · have e : p x + |p x - q x| = q x := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; ring
      have := abs_negMulLog_sub_le (hp.nonneg x) (abs_nonneg _) hx (by rw [e]; exact hq.le_one x)
      rwa [e] at this
    · have e : q x + |p x - q x| = p x := by
        rw [abs_of_nonneg (by linarith)]; ring
      have := abs_negMulLog_sub_le (hq.nonneg x) (abs_nonneg _) hx (by rw [e]; exact hp.le_one x)
      rwa [e, abs_sub_comm] at this
  calc |entropy p - entropy q| = |∑ x, (negMulLog (p x) - negMulLog (q x))| := by
        rw [entropy_eq_sum_negMulLog, entropy_eq_sum_negMulLog, sum_sub_distrib]
    _ ≤ ∑ x, |negMulLog (p x) - negMulLog (q x)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, negMulLog |p x - q x| := sum_le_sum fun x _ => hr x
    _ ≤ _ := sum_negMulLog_le fun x => abs_nonneg _

/-! ### Relative entropy and the `χ²` distance -/

/-- **Definition (17.35).** The `χ²` distance `χ²(P, Q) = ∑ₓ (P(x) - Q(x))²/Q(x)`. -/
def chiSq (P Q : α → ℝ) : ℝ := ∑ x, (P x - Q x) ^ 2 / Q x

lemma chiSq_add_mul (Q Δ : α → ℝ) (t : ℝ) :
    chiSq (fun x => Q x + t * Δ x) Q = t ^ 2 * ∑ x, Δ x ^ 2 / Q x := by
  simp only [chiSq, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  ring

/-- `|(1 + u) log (1 + u) - u - u²/2| ≤ 4|u|³` for `|u| ≤ 1/2`. -/
lemma abs_one_add_mul_log_sub_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |(1 + u) * log (1 + u) - u - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have h := abs_log_sub_add_sum_range_le (x := -u) (by rw [abs_neg]; linarith) 2
  simp only [sum_range_succ, sum_range_zero, abs_neg, sub_neg_eq_add] at h
  have hu3 : 0 ≤ |u| ^ 3 := by positivity
  set E := log (1 + u) - u + u ^ 2 / 2
  have hE : |E| ≤ 2 * |u| ^ 3 := by
    have h2 : |u| ^ 3 / (1 - |u|) ≤ 2 * |u| ^ 3 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    refine le_trans (le_of_eq ?_) (h.trans h2)
    congr 1
    simp only [E]
    ring
  have h1u : |1 + u| ≤ 3 / 2 := by
    rw [abs_le] at hu ⊢; constructor <;> linarith
  have e : (1 + u) * log (1 + u) - u - u ^ 2 / 2 = E * (1 + u) - u ^ 3 / 2 := by
    simp only [E]; ring
  rw [e]
  calc |E * (1 + u) - u ^ 3 / 2| ≤ |E| * |1 + u| + |u| ^ 3 / 2 := by
        refine (abs_sub _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_div, abs_pow]
        norm_num
    _ ≤ 2 * |u| ^ 3 * (3 / 2) + |u| ^ 3 / 2 := by gcongr
    _ ≤ 4 * |u| ^ 3 := by linarith

/-- **Lemma 17.3.3, (17.36).** Near `Q > 0`, the relative entropy is half the `χ²` distance: for
`P = Q + tΔ` with `∑ Δ = 0` and `|tΔ| ≤ Q/2`,
`|D(P ‖ Q) - χ²(P, Q)/2| ≤ 4|t|³ ∑ₓ |Δ(x)|³/Q(x)²`. -/
theorem abs_relEntropyReal_sub_chiSq_le {Q Δ : α → ℝ} (hQ : ∀ x, 0 < Q x) (hΔ : ∑ x, Δ x = 0)
    {t : ℝ} (ht : ∀ x, |t * Δ x| ≤ Q x / 2) :
    |relEntropyReal (fun x => Q x + t * Δ x) Q - chiSq (fun x => Q x + t * Δ x) Q / 2| ≤
      4 * |t| ^ 3 * ∑ x, |Δ x| ^ 3 / Q x ^ 2 := by
  set u : α → ℝ := fun x => t * Δ x / Q x
  have hu : ∀ x, |u x| ≤ 1 / 2 := by
    intro x
    rw [abs_div, abs_of_pos (hQ x), div_le_iff₀ (hQ x)]
    linarith [ht x]
  have hterm : ∀ x, (Q x + t * Δ x) * log ((Q x + t * Δ x) / Q x) -
      (Q x + t * Δ x - Q x) ^ 2 / Q x / 2 =
      Q x * ((1 + u x) * log (1 + u x) - u x - u x ^ 2 / 2) + t * Δ x := by
    intro x
    have hQx := (hQ x).ne'
    have htu : t * Δ x = Q x * u x := by simp only [u]; field_simp
    rw [htu, show (Q x + Q x * u x) / Q x = 1 + u x by field_simp]
    field_simp
    ring
  have hsum : relEntropyReal (fun x => Q x + t * Δ x) Q - chiSq (fun x => Q x + t * Δ x) Q / 2 =
      ∑ x, Q x * ((1 + u x) * log (1 + u x) - u x - u x ^ 2 / 2) := by
    rw [relEntropyReal, chiSq, sum_div, ← sum_sub_distrib]
    simp only [hterm, sum_add_distrib, ← mul_sum, hΔ, mul_zero, add_zero]
  rw [hsum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul, abs_of_pos (hQ x)]
  calc Q x * |(1 + u x) * log (1 + u x) - u x - u x ^ 2 / 2| ≤ Q x * (4 * |u x| ^ 3) :=
        mul_le_mul_of_nonneg_left (abs_one_add_mul_log_sub_le (hu x)) (hQ x).le
    _ = 4 * |t| ^ 3 * (|Δ x| ^ 3 / Q x ^ 2) := by
        have hQx := (hQ x).ne'
        simp only [u, abs_div, abs_mul, abs_of_pos (hQ x)]
        field_simp

/-- **Lemma 17.3.3, (17.36)**, as a limit: `D(Q + tΔ ‖ Q)/t² → (1/2) ∑ₓ Δ(x)²/Q(x)` as `t → 0`,
which is `χ²(Q + tΔ, Q)/(2t²)`. -/
theorem tendsto_relEntropyReal_div_sq {Q Δ : α → ℝ} (hQ : ∀ x, 0 < Q x) (hΔ : ∑ x, Δ x = 0) :
    Tendsto (fun t => relEntropyReal (fun x => Q x + t * Δ x) Q / t ^ 2) (𝓝[≠] 0)
      (𝓝 ((∑ x, Δ x ^ 2 / Q x) / 2)) := by
  set C := ∑ x, |Δ x| ^ 3 / Q x ^ 2
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ x, |t * Δ x| ≤ Q x / 2 := by
    refine nhdsWithin_le_nhds (eventually_all.2 fun x => ?_)
    have hc : Tendsto (fun t : ℝ => |t * Δ x|) (𝓝 0) (𝓝 0) := by
      have := ((continuous_id.mul continuous_const).abs.tendsto (0 : ℝ) :
        Tendsto (fun t : ℝ => |t * Δ x|) (𝓝 0) (𝓝 |0 * Δ x|))
      simpa using this
    exact (hc.eventually (ge_mem_nhds (by linarith [hQ x] : (0 : ℝ) < Q x / 2)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t : ℝ => 4 * |t| * C) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => 4 * |t| * C) (𝓝 0) (𝓝 (4 * |0| * C)) :=
      ((continuous_const.mul continuous_abs).mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
  have ht0' : t ≠ 0 := ht0
  have ht2 : 0 < t ^ 2 := by positivity
  have h := abs_relEntropyReal_sub_chiSq_le hQ hΔ ht
  rw [chiSq_add_mul] at h
  rw [Real.norm_eq_abs, show relEntropyReal (fun x => Q x + t * Δ x) Q / t ^ 2 -
      (∑ x, Δ x ^ 2 / Q x) / 2 =
      (relEntropyReal (fun x => Q x + t * Δ x) Q - t ^ 2 * (∑ x, Δ x ^ 2 / Q x) / 2) / t ^ 2 by
    field_simp, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
  calc _ ≤ 4 * |t| ^ 3 * C := h
    _ = 4 * |t| * C * t ^ 2 := by rw [← sq_abs t]; ring

/-! ### The expected relative entropy of the empirical distribution -/

omit [Fintype α] in
/-- The type of `x ∈ 𝒳ⁿ⁺¹` is the average of the types of the `n + 1` subsequences obtained by
removing one symbol. -/
lemma typeOf_eq_sum_removeNth {n : ℕ} (hn : 0 < n) (x : Fin (n + 1) → α) (a : α) :
    typeOf x a = ∑ j, (1 / ((n : ℝ) + 1)) * typeOf (Fin.removeNth j x) a := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set g : Fin (n + 1) → ℝ := fun i => if x i = a then 1 else 0
  have hj : ∀ j : Fin (n + 1), (symbolCount (Fin.removeNth j x) a : ℝ) =
      (symbolCount x a : ℝ) - g j := by
    intro j
    rw [symbolCount_eq_sum (Fin.removeNth j x), symbolCount_eq_sum x,
      Fin.sum_univ_succAbove _ j]
    simp only [g, Fin.removeNth, add_sub_cancel_left]
    congr
  have hS : ∑ j, g j = (symbolCount x a : ℝ) := (symbolCount_eq_sum x a).symm
  simp only [typeOf]
  simp_rw [hj]
  rw [← mul_sum, ← sum_div, sum_sub_distrib, hS]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- `s ↦ s log (s / c)` is convex on `[0, ∞)` for `c ≥ 0`. -/
lemma convexOn_mul_log_div {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ (Set.Ici 0) fun s => s * log (s / c) := by
  rcases hc.eq_or_lt with rfl | hc'
  · simp only [div_zero, log_zero, mul_zero]
    exact convexOn_const 0 (convex_Ici 0)
  have e : (fun s => s * log (s / c)) = fun s => s * log s + (-log c) * s := by
    funext s
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · rw [log_div hs hc'.ne']; ring
  rw [e]
  refine convexOn_mul_log.add ⟨convex_Ici 0, fun x _ y _ a b _ _ _ => le_of_eq ?_⟩
  simp only [smul_eq_mul]
  ring

/-- The expectation over `n + 1` i.i.d. symbols of a function of the sequence with the `j`-th
symbol removed. -/
lemma sum_iidPMF_mul_removeNth {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (j : Fin (n + 1))
    (g : (Fin n → α) → ℝ) :
    ∑ x, iidPMF p (n + 1) x * g (Fin.removeNth j x) = ∑ y, iidPMF p n y * g y := by
  rw [Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => α) j).symm _
    (fun q => p q.1 * (iidPMF p n q.2 * g q.2)) (fun x => ?_), Fintype.sum_prod_type]
  · simp only [← mul_sum]
    rw [← sum_mul, hp.sum_eq_one, one_mul]
  · simp only [Fin.insertNthEquiv_symm_apply, iidPMF_apply, Fin.prod_univ_succAbove _ j,
      Fin.removeNth]
    ring

/-- **Theorem 17.1.11, (17.16).** Let `p̂ₙ` be the empirical distribution (type) of `n` i.i.d.
samples of `p`. Then `E D(p̂ₙ₊₁ ‖ p) ≤ E D(p̂ₙ ‖ p)`. -/
theorem expect_relEntropy_typeOf_succ_le {p : α → ℝ} (hp : IsPMF p) {n : ℕ} (hn : 0 < n) :
    ∑ x : Fin (n + 1) → α, iidPMF p (n + 1) x * relEntropyReal (typeOf x) p ≤
      ∑ x : Fin n → α, iidPMF p n x * relEntropyReal (typeOf x) p := by
  set w : ℝ := 1 / ((n : ℝ) + 1)
  have hw : 0 ≤ w := by positivity
  have hw1 : ∑ _j : Fin (n + 1), w = 1 := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, w]
    push_cast
    field_simp
  -- Jensen: `D(p̂ₙ₊₁ ‖ p) ≤ (1/(n+1)) ∑ⱼ D(p̂ₙ⁽ʲ⁾ ‖ p)`.
  have hD : ∀ x : Fin (n + 1) → α, relEntropyReal (typeOf x) p ≤
      ∑ j, w * relEntropyReal (typeOf (Fin.removeNth j x)) p := by
    intro x
    simp only [relEntropyReal, mul_sum]
    rw [sum_comm]
    refine sum_le_sum fun a _ => ?_
    rw [typeOf_eq_sum_removeNth hn x a]
    exact (convexOn_mul_log_div (hp.nonneg a)).map_sum_le (fun j _ => hw) hw1
      (fun j _ => Set.mem_Ici.2 (typeOf_nonneg _ a))
  calc ∑ x : Fin (n + 1) → α, iidPMF p (n + 1) x * relEntropyReal (typeOf x) p
      ≤ ∑ x : Fin (n + 1) → α, iidPMF p (n + 1) x *
          ∑ j, w * relEntropyReal (typeOf (Fin.removeNth j x)) p :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hD x) (iidPMF_nonneg hp.nonneg x)
    _ = ∑ j : Fin (n + 1), w *
          ∑ x : Fin (n + 1) → α,
            iidPMF p (n + 1) x * relEntropyReal (typeOf (Fin.removeNth j x)) p := by
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun j _ => sum_congr rfl fun x _ => ?_
        ring
    _ = ∑ x : Fin n → α, iidPMF p n x * relEntropyReal (typeOf x) p := by
        have hj : ∀ j, ∑ x : Fin (n + 1) → α,
            iidPMF p (n + 1) x * relEntropyReal (typeOf (Fin.removeNth j x)) p =
            ∑ x : Fin n → α, iidPMF p n x * relEntropyReal (typeOf x) p := fun j =>
          sum_iidPMF_mul_removeNth hp j fun y => relEntropyReal (typeOf y) p
        simp only [hj, ← sum_mul, hw1, one_mul]

end InfoTheory
