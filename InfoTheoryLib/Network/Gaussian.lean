/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.Capacity

/-!
# Gaussian multiple-user channels

Section 15.1 describes the capacity regions of the Gaussian multiple-access, broadcast, relay,
interference and two-way channels in terms of the function `C(x) = ½ log (1 + x)`, the capacity
of a Gaussian channel with signal-to-noise ratio `x`. The coding theorems are stated there without
proof; this file proves the properties of the regions that the book derives from the formulas.

## Main definitions

* `gaussCap x`: **(15.5), (15.146)** `C(x) = ½ log (1 + x)`.
* `gaussianMACRegion P N`: **(15.6)–(15.10), (15.153)** the rate vectors `R` of an `m`-user
  Gaussian multiple-access channel with `∑_{i ∈ S} Rᵢ ≤ C(∑_{i ∈ S} Pᵢ / N)` for all `S`.
* `gaussianBCRegion P N₁ N₂`: **(15.11)–(15.12)** the capacity region of the Gaussian broadcast
  channel.
* `gaussianRelayRate`, `gaussianRelayCapacity`: **(15.16)** the capacity of the Gaussian relay
  channel.
* `fdmaRate W P N`: **(15.150)–(15.151)** the rate `W log (1 + P/(N W))` of a user with bandwidth
  `W` in frequency-division multiple access.

## Main statements

* `gaussianInfoCapacity_eq_gaussCap`: `C(P/N)` is the capacity of the Gaussian channel (15.3).
* `gaussCap_add_gaussCap`: onion peeling, `C(P₁/N) + C(P₂/(P₁ + N)) = C((P₁ + P₂)/N)`: the corner
  points of the Gaussian multiple-access region (Section 15.3.6).
* `const_mem_gaussianMACRegion`: with equal powers and equal rates, the last inequality (15.10)
  dominates the others.
* `tendsto_gaussCap_mul_atTop`, `tendsto_gaussCap_mul_div_atTop`: the sum rate `C(mP/N)` tends to
  `∞` with `m` while the rate per user `C(mP/N)/m` tends to `0`.
* `gaussianBC_sum_ge`: superposition beats sending to the worse receiver alone.
* `gaussianRelayCapacity_eq`: **(15.17)** if `P₁/N₂ ≥ P/N₁`, the relay channel has capacity
  `C(P/N₁)`.
* `gaussCap_lt_iff_strong_interference`: the condition `C(a²P/(P + N)) > C(P/N)` of high
  interference, Section 15.1.5.
* `fdmaRate_add_le`, `fdmaRate_add_eq`: frequency-division multiplexing reaches the sum capacity
  only when the bandwidths are proportional to the powers (Figure 15.18); `tdma_le`, `tdma_eq`:
  the same for time division with power boosting.
* `gaussCap_noise_le_tdma`: time division with power control at `t = S₁/(S₁ + S₂)` beats treating
  the other codeword as noise ([elgamal2010], Lecture 4).

## Implementation notes

The regions are sets of rates in nats; the book writes them with strict inequalities, which give
the same closure. Powers and noise variances are real numbers, with positivity hypotheses where
needed.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 15.1 and
  15.3.6
* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 4
-/

open Real Finset Filter Topology
open scoped NNReal

@[expose] public noncomputable section

namespace InfoTheory

/-- **(15.5), (15.146)** The capacity `C(x) = ½ log (1 + x)` of a Gaussian channel with
signal-to-noise ratio `x`. -/
def gaussCap (x : ℝ) : ℝ := 1 / 2 * log (1 + x)

/-- **(15.3)** `C(P/N)` is the capacity of the Gaussian channel with power `P` and noise `N`. -/
theorem gaussianInfoCapacity_eq_gaussCap (P : ℝ≥0) {N : ℝ≥0} (hN : N ≠ 0) :
    gaussianInfoCapacity P N = gaussCap (P / N) :=
  gaussianInfoCapacity_eq P hN

@[simp] lemma gaussCap_zero : gaussCap 0 = 0 := by simp [gaussCap]

lemma gaussCap_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gaussCap x :=
  mul_nonneg (by norm_num) (log_nonneg (by linarith))

lemma gaussCap_le_gaussCap {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : gaussCap x ≤ gaussCap y :=
  mul_le_mul_of_nonneg_left (log_le_log (by linarith) (by linarith)) (by norm_num)

lemma gaussCap_lt_gaussCap {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : gaussCap x < gaussCap y :=
  mul_lt_mul_of_pos_left (log_lt_log (by linarith) (by linarith)) (by norm_num)

lemma gaussCap_lt_gaussCap_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    gaussCap x < gaussCap y ↔ x < y :=
  ⟨fun h => lt_of_not_ge fun h' => (gaussCap_le_gaussCap hy h').not_gt h,
    gaussCap_lt_gaussCap hx⟩

/-- **Onion peeling (Section 15.3.6).** Decoding the second sender first, with the first as
noise, and then the first: `C(P₁/N) + C(P₂/(P₁ + N)) = C((P₁ + P₂)/N)`. -/
theorem gaussCap_add_gaussCap {P₁ P₂ N : ℝ} (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    gaussCap (P₁ / N) + gaussCap (P₂ / (P₁ + N)) = gaussCap ((P₁ + P₂) / N) := by
  have h1 : 1 + P₁ / N = (P₁ + N) / N := by field_simp; ring
  have h2 : 1 + P₂ / (P₁ + N) = (P₁ + N + P₂) / (P₁ + N) := by field_simp
  have h3 : 1 + (P₁ + P₂) / N = (P₁ + N) / N * ((P₁ + N + P₂) / (P₁ + N)) := by
    field_simp; ring
  have hpos : 0 < P₁ + N := by linarith
  rw [gaussCap, gaussCap, gaussCap, h1, h2, h3, log_mul (by positivity) (by positivity)]
  ring

/-- Concavity of `C` with `C(0) = 0`: `t C(x) ≤ C(t x)` for `0 ≤ t ≤ 1`. -/
lemma mul_gaussCap_le {t x : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (hx : 0 ≤ x) :
    t * gaussCap x ≤ gaussCap (t * x) := by
  have h := (strictConcaveOn_log_Ioi.concaveOn).2 (x := 1 + x) (y := 1) (by simp; linarith)
    (by simp) ht₀ (by linarith : 0 ≤ 1 - t) (by ring)
  simp only [smul_eq_mul, log_one, mul_zero, add_zero] at h
  have : t * (1 + x) + (1 - t) * 1 = 1 + t * x := by ring
  rw [this] at h
  unfold gaussCap
  nlinarith

/-! ### The Gaussian multiple-access channel -/

/-- **(15.6)–(15.10), (15.153)** The capacity region of the `m`-user Gaussian multiple-access
channel with powers `P₁, …, Pₘ` and noise `N`: `∑_{i ∈ S} Rᵢ ≤ C(∑_{i ∈ S} Pᵢ / N)` for every set
`S` of users. -/
def gaussianMACRegion {m : ℕ} (P : Fin m → ℝ) (N : ℝ) : Set (Fin m → ℝ) :=
  {R | ∀ S : Finset (Fin m), ∑ i ∈ S, R i ≤ gaussCap ((∑ i ∈ S, P i) / N)}

/-- **(15.147)–(15.149)** For two users, the region is `R₁ ≤ C(P₁/N)`, `R₂ ≤ C(P₂/N)`,
`R₁ + R₂ ≤ C((P₁ + P₂)/N)`. -/
theorem mem_gaussianMACRegion_two {P : Fin 2 → ℝ} {N : ℝ} {R : Fin 2 → ℝ} :
    R ∈ gaussianMACRegion P N ↔ R 0 ≤ gaussCap (P 0 / N) ∧ R 1 ≤ gaussCap (P 1 / N) ∧
      R 0 + R 1 ≤ gaussCap ((P 0 + P 1) / N) := by
  constructor
  · intro h
    refine ⟨by simpa using h {0}, by simpa using h {1}, by simpa using h univ⟩
  · rintro ⟨h0, h1, h01⟩ S
    have hS : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = univ := by
      by_cases a : (0 : Fin 2) ∈ S <;> by_cases b : (1 : Fin 2) ∈ S
      · right; right; right; ext i; fin_cases i <;> simp [a, b]
      · right; left; ext i; fin_cases i <;> simp [a, b]
      · right; right; left; ext i; fin_cases i <;> simp [a, b]
      · left; ext i; fin_cases i <;> simp [a, b]
    rcases hS with rfl | rfl | rfl | rfl
    · simp
    · simpa using h0
    · simpa using h1
    · simpa using h01

/-- **Corner point (Figure 15.17).** Onion peeling achieves the corner point
`(C(P₁/N), C(P₂/(P₁ + N)))` of the two-user region, on the sum-rate boundary. -/
theorem corner_mem_gaussianMACRegion {P : Fin 2 → ℝ} {N : ℝ} (hP : ∀ i, 0 ≤ P i) (hN : 0 < N) :
    ![gaussCap (P 0 / N), gaussCap (P 1 / (P 0 + N))] ∈ gaussianMACRegion P N := by
  rw [mem_gaussianMACRegion_two]
  refine ⟨by simp, ?_, by simp [gaussCap_add_gaussCap (hP 0) (hP 1) hN]⟩
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  exact gaussCap_le_gaussCap (div_nonneg (hP 1) (by linarith [hP 0]))
    (div_le_div_of_nonneg_left (hP 1) hN (by linarith [hP 0]))

/-- **(15.6)–(15.10)** With equal powers `P` and equal rates `r`, the last inequality
`m r ≤ C(mP/N)` implies all the others. -/
theorem const_mem_gaussianMACRegion {m : ℕ} {P N r : ℝ} (hP : 0 ≤ P) (hN : 0 < N)
    (hr : m * r ≤ gaussCap (m * P / N)) :
    (fun _ => r) ∈ gaussianMACRegion (fun _ : Fin m => P) N := by
  intro S
  simp only [sum_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : S = ∅ := Subsingleton.elim _ _
    simp [this]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : (#S : ℝ) ≤ m := by exact_mod_cast (card_le_univ S).trans (by simp)
  set t := (#S : ℝ) / m
  have ht₀ : 0 ≤ t := by positivity
  have ht₁ : t ≤ 1 := (div_le_one hm').2 hk
  have h := mul_gaussCap_le ht₀ ht₁ (by positivity : 0 ≤ m * P / N)
  have e1 : #S * r = t * (m * r) := by simp only [t]; field_simp
  have e2 : t * (m * P / N) = #S * P / N := by simp only [t]; field_simp
  rw [e1, ← e2]
  exact (mul_le_mul_of_nonneg_left hr ht₀).trans h

/-- **Section 15.1.2** The sum rate `C(mP/N)` of `m` users of power `P` tends to infinity with
`m`: the cocktail party. -/
theorem tendsto_gaussCap_mul_atTop {P N : ℝ} (hP : 0 < P) (hN : 0 < N) :
    Tendsto (fun m : ℕ => gaussCap (m * P / N)) atTop atTop := by
  have h : Tendsto (fun m : ℕ => 1 + m * P / N) atTop atTop := by
    refine tendsto_atTop_add_const_left _ 1 ?_
    simp_rw [mul_div_assoc]
    exact tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  exact (tendsto_log_atTop.comp h).const_mul_atTop (by norm_num)

/-- **Section 15.3.6** The rate per user `C(mP/N)/m` tends to `0`. -/
theorem tendsto_gaussCap_mul_div_atTop {P N : ℝ} (hP : 0 < P) (hN : 0 < N) :
    Tendsto (fun m : ℕ => gaussCap (m * P / N) / m) atTop (𝓝 0) := by
  set c := P / N
  have hc : 0 < c := by positivity
  have h := tendsto_pow_log_div_mul_add_atTop (1 / c) (-(1 / c)) 1 (by positivity)
  have hx : Tendsto (fun m : ℕ => 1 + m * c) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
  have h2 := (h.comp hx).const_mul (1 / 2)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Function.comp, pow_one, gaussCap, c, mul_div_assoc]
  field_simp
  ring

/-! ### Frequency- and time-division multiple access -/

/-- The superadditivity of the perspective of `log (1 + ·)`:
`a log (1 + x/a) + b log (1 + y/b) ≤ (a + b) log (1 + (x + y)/(a + b))`. -/
lemma mul_log_add_mul_log_le {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a * log (1 + x / a) + b * log (1 + y / b) ≤ (a + b) * log (1 + (x + y) / (a + b)) := by
  have hs : 0 < a + b := by positivity
  have h := (strictConcaveOn_log_Ioi.concaveOn).2 (x := 1 + x / a) (y := 1 + y / b)
    (by simp only [Set.mem_Ioi]; positivity) (by simp only [Set.mem_Ioi]; positivity)
    (div_nonneg ha.le hs.le)
    (div_nonneg hb.le hs.le) (by field_simp)
  simp only [smul_eq_mul] at h
  have e : a / (a + b) * (1 + x / a) + b / (a + b) * (1 + y / b) = 1 + (x + y) / (a + b) := by
    field_simp; ring
  rw [e] at h
  have := mul_le_mul_of_nonneg_left h hs.le
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_div_cancel₀ _ hs.ne', mul_div_cancel₀ _ hs.ne']
    at this
  exact this

lemma mul_log_add_mul_log_eq {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) (hxy : x * b = y * a) :
    a * log (1 + x / a) + b * log (1 + y / b) = (a + b) * log (1 + (x + y) / (a + b)) := by
  have hs : 0 < a + b := by positivity
  have h1 : y / b = x / a := by rw [div_eq_div_iff hb.ne' ha.ne']; linarith
  have h2 : (x + y) / (a + b) = x / a := by
    rw [div_eq_div_iff hs.ne' ha.ne']; linarith
  rw [h1, h2]
  ring

/-- **(15.150)–(15.151)** The rate `W log (1 + P/(N W))` of a user with bandwidth `W` and power
`P` in frequency-division multiple access. -/
def fdmaRate (W P N : ℝ) : ℝ := W * log (1 + P / (N * W))

/-- **Figure 15.18** Frequency-division multiplexing does at most as well as one user with the
total power and the total bandwidth. -/
theorem fdmaRate_add_le {W₁ W₂ P₁ P₂ N : ℝ} (hW₁ : 0 < W₁) (hW₂ : 0 < W₂) (hP₁ : 0 ≤ P₁)
    (hP₂ : 0 ≤ P₂) (hN : 0 < N) :
    fdmaRate W₁ P₁ N + fdmaRate W₂ P₂ N ≤ fdmaRate (W₁ + W₂) (P₁ + P₂) N := by
  have h := mul_log_add_mul_log_le hW₁ hW₂ (div_nonneg hP₁ hN.le) (div_nonneg hP₂ hN.le)
  simp only [fdmaRate]
  convert h using 3 <;> field_simp

/-- **Figure 15.18** Frequency-division multiplexing reaches the sum capacity when the bandwidths
are proportional to the powers. -/
theorem fdmaRate_add_eq {W₁ W₂ P₁ P₂ N : ℝ} (hW₁ : 0 < W₁) (hW₂ : 0 < W₂) (hN : 0 < N)
    (h : P₁ * W₂ = P₂ * W₁) :
    fdmaRate W₁ P₁ N + fdmaRate W₂ P₂ N = fdmaRate (W₁ + W₂) (P₁ + P₂) N := by
  have h' := mul_log_add_mul_log_eq (x := P₁ / N) (y := P₂ / N) hW₁ hW₂
    (by field_simp; linarith)
  simp only [fdmaRate]
  convert h' using 3 <;> field_simp

/-- **Section 15.3.6** Time division with power boosting: user 1 sends with power `P₁/t` a
fraction `t` of the time and user 2 with power `P₂/(1 - t)` the rest of the time. The sum rate is
at most `C((P₁ + P₂)/N)`. -/
theorem tdma_le {t P₁ P₂ N : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hN : 0 < N) :
    t * gaussCap (P₁ / (t * N)) + (1 - t) * gaussCap (P₂ / ((1 - t) * N)) ≤
      gaussCap ((P₁ + P₂) / N) := by
  have h := mul_log_add_mul_log_le ht₀ (by linarith : 0 < 1 - t) (div_nonneg hP₁ hN.le)
    (div_nonneg hP₂ hN.le)
  have e1 : P₁ / N / t = P₁ / (t * N) := by field_simp
  have e2 : P₂ / N / (1 - t) = P₂ / ((1 - t) * N) := by field_simp
  rw [e1, e2, add_sub_cancel, one_mul, ← add_div, div_one] at h
  unfold gaussCap
  calc t * (1 / 2 * log (1 + P₁ / (t * N))) + (1 - t) * (1 / 2 * log (1 + P₂ / ((1 - t) * N)))
      = 1 / 2 * (t * log (1 + P₁ / (t * N)) + (1 - t) * log (1 + P₂ / ((1 - t) * N))) := by ring
    _ ≤ _ := by gcongr

/-- **Section 15.3.6** Time division with power boosting reaches the sum capacity for
`t = P₁/(P₁ + P₂)`. -/
theorem tdma_eq {t P₁ P₂ N : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) (hN : 0 < N)
    (h : P₁ * (1 - t) = P₂ * t) :
    t * gaussCap (P₁ / (t * N)) + (1 - t) * gaussCap (P₂ / ((1 - t) * N)) =
      gaussCap ((P₁ + P₂) / N) := by
  have h' := mul_log_add_mul_log_eq (x := P₁ / N) (y := P₂ / N) ht₀ (by linarith : 0 < 1 - t)
    (by field_simp; linarith)
  have e1 : P₁ / N / t = P₁ / (t * N) := by field_simp
  have e2 : P₂ / N / (1 - t) = P₂ / ((1 - t) * N) := by field_simp
  rw [e1, e2, add_sub_cancel, one_mul, ← add_div, div_one] at h'
  unfold gaussCap
  rw [← h']
  ring

/-- **Section 15.3.6** Naive time division, each of two users of power `P` sending half the time
with power `P`, does worse than sending half the time with power `2P`. -/
theorem naive_tdma_le {P N : ℝ} (hP : 0 ≤ P) (hN : 0 < N) :
    1 / 2 * gaussCap (P / N) ≤ 1 / 2 * gaussCap (2 * P / N) :=
  mul_le_mul_of_nonneg_left (gaussCap_le_gaussCap (by positivity)
    (div_le_div_of_nonneg_right (by linarith) hN.le)) (by norm_num)

/-! ### The Gaussian broadcast channel -/

/-- **(15.11)–(15.12)** The capacity region of the Gaussian broadcast channel with power `P` and
noises `N₁ ≤ N₂`: `R₁ ≤ C(αP/N₁)`, `R₂ ≤ C((1 - α)P/(αP + N₂))` for some `0 ≤ α ≤ 1`. -/
def gaussianBCRegion (P N₁ N₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ α ∈ Set.Icc (0 : ℝ) 1, R.1 ≤ gaussCap (α * P / N₁) ∧
    R.2 ≤ gaussCap ((1 - α) * P / (α * P + N₂))}

/-- With `α = 1`, all the power goes to the first receiver; with `α = 0`, to the second. -/
theorem mem_gaussianBCRegion_of_single (P N₁ N₂ : ℝ) :
    (gaussCap (P / N₁), 0) ∈ gaussianBCRegion P N₁ N₂ ∧
      (0, gaussCap (P / N₂)) ∈ gaussianBCRegion P N₁ N₂ :=
  ⟨⟨1, by simp, by simp, by simp⟩, ⟨0, by simp, by simp, by simp⟩⟩

/-- **Section 15.1.3** Superposition coding: if `N₁ ≤ N₂`, every split `α` of the power gives a
sum rate at least `C(P/N₂)`, the rate of sending to the worse receiver alone. -/
theorem gaussianBC_sum_ge {P N₁ N₂ α : ℝ} (hP : 0 ≤ P) (hN₁ : 0 < N₁) (hN : N₁ ≤ N₂)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    gaussCap (P / N₂) ≤ gaussCap (α * P / N₁) + gaussCap ((1 - α) * P / (α * P + N₂)) := by
  have hN₂ : 0 < N₂ := by linarith
  have hαP : 0 ≤ α * P := mul_nonneg hα.1 hP
  have h1α : 0 ≤ 1 - α := by linarith [hα.2]
  have h := gaussCap_add_gaussCap hαP (mul_nonneg h1α hP) hN₂
  have e : α * P + (1 - α) * P = P := by ring
  rw [e] at h
  rw [← h]
  have : gaussCap (α * P / N₂) ≤ gaussCap (α * P / N₁) :=
    gaussCap_le_gaussCap (by positivity) (div_le_div_of_nonneg_left hαP hN₁ hN)
  linarith

/-! ### The Gaussian relay channel -/

/-- **(15.16)** The rate `min {C((P + P₁ + 2√(ᾱ P P₁))/(N₁ + N₂)), C(αP/N₁)}` of the Gaussian relay
channel for the split `α`, with `ᾱ = 1 - α`. -/
def gaussianRelayRate (P P₁ N₁ N₂ α : ℝ) : ℝ :=
  min (gaussCap ((P + P₁ + 2 * √((1 - α) * P * P₁)) / (N₁ + N₂))) (gaussCap (α * P / N₁))

/-- **(15.16)** The capacity `C = max_{0 ≤ α ≤ 1} min {…}` of the Gaussian relay channel. -/
def gaussianRelayCapacity (P P₁ N₁ N₂ : ℝ) : ℝ :=
  sSup (gaussianRelayRate P P₁ N₁ N₂ '' Set.Icc 0 1)

/-- **(15.17)** If `P₁/N₂ ≥ P/N₁`, the capacity of the Gaussian relay channel is `C(P/N₁)`,
achieved by `α = 1`: the channel appears noise-free after the relay. -/
theorem gaussianRelayCapacity_eq {P P₁ N₁ N₂ : ℝ} (hP : 0 ≤ P) (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) (h : P / N₁ ≤ P₁ / N₂) :
    gaussianRelayCapacity P P₁ N₁ N₂ = gaussCap (P / N₁) := by
  refine IsGreatest.csSup_eq ⟨⟨1, by simp, ?_⟩, ?_⟩
  · simp only [gaussianRelayRate, sub_self, zero_mul, Real.sqrt_zero, mul_zero, add_zero,
      one_mul]
    refine min_eq_right (gaussCap_le_gaussCap (by positivity) ?_)
    rw [div_le_div_iff₀ hN₁ (by positivity)]
    rw [div_le_div_iff₀ hN₁ hN₂] at h
    nlinarith
  · rintro _ ⟨α, hα, rfl⟩
    refine (min_le_right _ _).trans (gaussCap_le_gaussCap (by positivity [hα.1]) ?_)
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hP hα.2) hN₁.le

/-- **Section 15.1.4** The relay helps: the rate `C(P/(N₁ + N₂))` without the relay is at most the
capacity `C(P/N₁)` with it. -/
theorem gaussCap_le_gaussianRelayCapacity {P P₁ N₁ N₂ : ℝ} (hP : 0 ≤ P) (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂) (h : P / N₁ ≤ P₁ / N₂) :
    gaussCap (P / (N₁ + N₂)) ≤ gaussianRelayCapacity P P₁ N₁ N₂ := by
  rw [gaussianRelayCapacity_eq hP hN₁ hN₂ h]
  exact gaussCap_le_gaussCap (by positivity) (div_le_div_of_nonneg_left hP hN₁ (by linarith))

/-! ### The Gaussian interference channel -/

/-- **Section 15.1.5** The condition of high interference `C(a²P/(P + N)) > C(P/N)`, under which
each receiver can decode the interfering message first, is `a² > 1 + P/N`. -/
theorem gaussCap_lt_iff_strong_interference {a P N : ℝ} (hP : 0 < P) (hN : 0 < N) :
    gaussCap (P / N) < gaussCap (a ^ 2 * P / (P + N)) ↔ 1 + P / N < a ^ 2 := by
  rw [gaussCap_lt_gaussCap_iff (by positivity) (by positivity), div_lt_div_iff₀ hN (by positivity)]
  rw [← sub_pos, ← sub_pos (a := a ^ 2)]
  have e : a ^ 2 * P * N - P * (P + N) = P * N * (a ^ 2 - (1 + P / N)) := by
    field_simp; ring
  rw [e]
  exact ⟨fun h => pos_of_mul_pos_right h (by positivity), fun h => by positivity⟩

/-- `C(x) ≤ x/2`. -/
lemma gaussCap_le_half {x : ℝ} (hx : 0 ≤ x) : gaussCap x ≤ x / 2 := by
  have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
  unfold gaussCap
  linarith

/-- `C(x) ≥ x / (2 (1 + x))`. -/
lemma div_le_gaussCap {x : ℝ} (hx : 0 ≤ x) : x / (2 * (1 + x)) ≤ gaussCap x := by
  have h := one_sub_inv_le_log_of_pos (by linarith : (0 : ℝ) < 1 + x)
  have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
  rw [e] at h
  unfold gaussCap
  rw [show x / (2 * (1 + x)) = 1 / 2 * (x / (1 + x)) by field_simp]
  linarith

/-- **TDMA with power control (Lecture 4 of [elgamal2010]).** With received SNRs `S₁, S₂ > 0` and
`t = S₁/(S₁ + S₂)`, time division with power control, which gives sender 1 the rate
`t C(S₁/t)` and sender 2 the rate `(1 - t) C(S₂/(1 - t))`, beats treating the other codeword as
noise, which gives the rates `C(S₁/(1 + S₂))` and `C(S₂/(1 + S₁))`. -/
theorem gaussCap_noise_le_tdma {S₁ S₂ : ℝ} (h₁ : 0 < S₁) (h₂ : 0 < S₂) :
    gaussCap (S₁ / (1 + S₂)) ≤ S₁ / (S₁ + S₂) * gaussCap (S₁ / (S₁ / (S₁ + S₂))) ∧
      gaussCap (S₂ / (1 + S₁)) ≤
        (1 - S₁ / (S₁ + S₂)) * gaussCap (S₂ / (1 - S₁ / (S₁ + S₂))) := by
  have hs : 0 < S₁ + S₂ := by linarith
  have e₁ : S₁ / (S₁ / (S₁ + S₂)) = S₁ + S₂ := by field_simp
  have e₂ : 1 - S₁ / (S₁ + S₂) = S₂ / (S₁ + S₂) := by field_simp; ring
  have e₃ : S₂ / (S₂ / (S₁ + S₂)) = S₁ + S₂ := by field_simp
  rw [e₁, e₂, e₃]
  -- `C(S₁ + S₂) = C(Sⱼ) + C(Sᵢ/(1 + Sⱼ))`, and `Sⱼ C(Sᵢ/(1 + Sⱼ)) ≤ Sᵢ C(Sⱼ)`.
  have key : ∀ {a b : ℝ}, 0 < a → 0 < b →
      gaussCap (a / (1 + b)) ≤ a / (a + b) * gaussCap (a + b) := fun {a b} ha hb => by
    have hab : 0 < a + b := by linarith
    have hsum := gaussCap_add_gaussCap hb.le ha.le one_pos
    rw [div_one, div_one, show a / (b + 1) = a / (1 + b) by ring, add_comm b a] at hsum
    have hu := gaussCap_le_half (by positivity : 0 ≤ a / (1 + b))
    have hl := div_le_gaussCap hb.le
    have h3 : b * gaussCap (a / (1 + b)) ≤ a * gaussCap b := by
      calc b * gaussCap (a / (1 + b)) ≤ b * (a / (1 + b) / 2) :=
            mul_le_mul_of_nonneg_left hu hb.le
        _ = a * (b / (2 * (1 + b))) := by field_simp
        _ ≤ a * gaussCap b := mul_le_mul_of_nonneg_left hl ha.le
    rw [← hsum, div_mul_eq_mul_div, le_div_iff₀ hab]
    nlinarith [h3]
  exact ⟨key h₁ h₂, by simpa [add_comm] using key h₂ h₁⟩

end InfoTheory
