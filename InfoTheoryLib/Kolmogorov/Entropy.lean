/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Kolmogorov.BinaryStrings
public import InfoTheoryLib.SourceCoding.OptimalLength
public import InfoTheoryLib.Statistics.Bernoulli
public import InfoTheoryLib.Statistics.LargeDeviations
public import InfoTheoryLib.RelativeEntropy.Pinsker
public import InfoTheoryLib.AEP.Basic

/-!
# Kolmogorov complexity, entropy and randomness

The shortest programs of the strings of length `n` form a prefix code, so the expected
Kolmogorov complexity of a random string is at least its entropy; the two-part program of
Theorem 14.2.5 shows that it is at most the entropy plus `O(log n)` for a Bernoulli source, so
that `(1/n) E K(Xⁿ | n) → H₀(θ)` (Theorem 14.3.1). Counting programs shows that most strings are
incompressible (Theorem 14.5.1), that there are infinitely many integers `n` with
`K(n) > log n` (Theorem 14.4.3), and the two-part program shows that the proportion of ones in
an incompressible sequence tends to `½` (Theorem 14.5.2).

## Main definitions

* `bitsOf x`: the binary string of a sequence `x : Fin n → Bool`.
* `natString n`: the binary string of the integer `n` (the digits of `n + 1` after the leading
  one), and `Computer.natComplexity U n = K(n)` (14.38).
* `IsIncompressible U x`: `K(x₁ ⋯ xₙ | n)/n → 1` (14.51).

## Main statements

* `entropy_le_expected_complexity`: **(14.29)**, `E K(Xⁿ | n) ≥ H(Xⁿ)`, for any distribution.
* `expected_complexity_le`: **(14.30)–(14.33)**, `E K(Xⁿ | n) ≤ n H₀(θ) + log₂ (n + 1) + c`.
* `tendsto_expected_complexity_div`: **Theorem 14.3.1**, `(1/n) E K(Xⁿ | n) → H₀(θ)`, and
  `tendsto_expected_complexity_div'`: **(14.36)–(14.37)**, the same without conditioning.
* `natComplexity_le`: **Theorem 14.4.2**, `K(n) ≤ log₂ (n + 1) + 2 log₂ (log₂ (n + 1) + 1) + c`.
* `exists_natComplexity_gt`: **Theorem 14.4.3**, `K(n) > log₂ n` for infinitely many `n`.
* `prob_complexity_lt_le`: **Theorem 14.5.1**, `Pr{K(Xⁿ | n) < n - k} < 2^{-k}`.
* `exists_random`: **(14.50)**, some `xⁿ` has `K(xⁿ | n) ≥ n`.
* `IsIncompressible.tendsto_ones_div`: **Theorem 14.5.2**.

## Implementation notes

The upper bound of Theorem 14.3.1 is proved for binary alphabets (Bernoulli sources), as the
book does in detail; the lower bound holds for every distribution. Complexities are in bits, so
entropies are taken in base `2`: `H₀(θ) = binEntropy θ / log 2`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 14.3–14.5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Sequences as strings -/

/-- The binary string `x₁ ⋯ xₙ` of a sequence `x : Fin n → Bool`. -/
abbrev bitsOf {n : ℕ} (x : Fin n → Bool) : List Bool := List.ofFn x

lemma ones_ofFn {n : ℕ} (x : Fin n → Bool) : ones (List.ofFn x) = onesCount x := by
  induction n with
  | zero => simp [ones, onesCount]
  | succ n ih =>
    rw [List.ofFn_succ, ones_cons, ih, onesCount, onesCount, Fin.sum_univ_succ, add_comm]

lemma injective_ofFn {n : ℕ} : Function.Injective (List.ofFn : (Fin n → Bool) → List Bool) :=
  List.ofFn_injective

/-- The complexities of the strings of length `n` satisfy the Kraft inequality. -/
lemma sum_two_rpow_neg_complexity_le_one {U : Computer} (hU : U.IsUniversal) (n y : ℕ) :
    ∑ x : Fin n → Bool, (2 : ℝ) ^ (-(U.complexity (List.ofFn x) y : ℝ)) ≤ 1 := by
  classical
  have h := U.sum_two_pow_neg_complexity_le_one y
    (univ.image (List.ofFn : (Fin n → Bool) → List Bool)) fun x _ => hU.hasProgram_all x y
  rw [sum_image fun a _ b _ hab => injective_ofFn hab] at h
  refine le_trans (le_of_eq (sum_congr rfl fun x _ => ?_)) h
  rw [rpow_neg (by norm_num), rpow_natCast, one_div, inv_pow]

/-! ### Theorem 14.3.1 -/

/-- **(14.29)** The expected complexity of a string of length `n` is at least its entropy (in
bits), for every distribution `p` of the string: `E K(Xⁿ | y) ≥ H(Xⁿ)`. -/
theorem entropy_le_expected_complexity {U : Computer} (hU : U.IsUniversal) {n : ℕ}
    {p : (Fin n → Bool) → ℝ} (hp : IsPMF p) (y : ℕ) :
    entropyBase 2 p ≤ ∑ x, p x * U.complexity (List.ofFn x) y :=
  (entropyBase_le_sum_mul_real hp (le_refl 2) (fun x => (U.complexity (List.ofFn x) y : ℝ))
    (by exact_mod_cast sum_two_rpow_neg_complexity_le_one hU n y)).1

/-- The mean number of ones of `n` Bernoulli(`θ`) trials is `n θ`. -/
lemma sum_iidPMF_mul_onesCount (θ : ℝ) (n : ℕ) :
    ∑ x : Fin n → Bool, iidPMF (bernoulliPMF θ) n x * onesCount x = n * θ := by
  have h : ∀ i : Fin n, ∑ x : Fin n → Bool, iidPMF (bernoulliPMF θ) n x * (if x i then 1 else 0)
      = θ := fun i => by
    have := sum_iidPMF_mul_prod (bernoulliPMF θ)
      (fun j (b : Bool) => if j = i then (if b then (1 : ℝ) else 0) else 1)
    simp only [prod_ite_eq', mem_univ, ite_true] at this
    rw [this]
    rw [prod_eq_single i fun j _ hj => by simp [hj, bernoulliPMF]]
    · simp [bernoulliPMF]
    · simp
  have e : ∀ x : Fin n → Bool, (onesCount x : ℝ) = ∑ i, if x i then (1 : ℝ) else 0 :=
    fun x => by simp [onesCount]
  simp_rw [e, mul_sum]
  rw [sum_comm, sum_congr rfl fun i _ => h i]
  simp

/-- **(14.30)–(14.33)** For `n` Bernoulli(`θ`) trials, `E K(Xⁿ | n) ≤ n H₀(θ) + log₂ (n + 1) + c`:
the two-part program and Jensen's inequality for the concave function `H₀`. -/
theorem expected_complexity_le {U : Computer} (hU : U.IsUniversal) :
    ∃ c : ℝ, ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → ∀ n : ℕ,
      ∑ x : Fin n → Bool, iidPMF (bernoulliPMF θ) n x * U.complexity (List.ofFn x) n ≤
        n * (binEntropy θ / log 2) + logb 2 (n + 1) + c := by
  obtain ⟨c, hc⟩ := complexity_le_binEntropy hU
  refine ⟨c, fun {θ} h0 h1 n => ?_⟩
  have hp := iidPMF_isPMF (bernoulliPMF_isPMF h0 h1) n
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hpt : ∀ x : Fin n → Bool, (U.complexity (List.ofFn x) n : ℝ) ≤
      n * (binEntropy (onesCount x / n) / log 2) + logb 2 (n + 1) + c := fun x => by
    have := hc (List.ofFn x)
    simpa [ones_ofFn] using this
  calc ∑ x, iidPMF (bernoulliPMF θ) n x * U.complexity (List.ofFn x) n
      ≤ ∑ x, iidPMF (bernoulliPMF θ) n x *
          (n * (binEntropy (onesCount x / n) / log 2) + logb 2 (n + 1) + c) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hp.nonneg x)
    _ = n / log 2 * ∑ x, iidPMF (bernoulliPMF θ) n x * binEntropy (onesCount x / n) +
          (logb 2 (n + 1) + c) := by
        simp only [mul_add, sum_add_distrib, ← sum_mul, hp.sum_eq_one, one_mul, mul_sum]
        rw [add_assoc]
        congr 1
        refine sum_congr rfl fun x _ => ?_
        ring
    _ ≤ n / log 2 * binEntropy θ + (logb 2 (n + 1) + c) := by
        gcongr
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · -- One string of length `0`.
          have : ∑ x : Fin 0 → Bool, iidPMF (bernoulliPMF θ) 0 x *
              binEntropy ((onesCount x : ℝ) / ((0 : ℕ) : ℝ)) = 0 := by simp
          rw [this]
          exact binEntropy_nonneg h0 h1
        -- Jensen's inequality for the concave binary entropy.
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        have hJ := strictConcave_binEntropy.concaveOn.le_map_sum (t := univ)
          (w := iidPMF (bernoulliPMF θ) n) (p := fun x => (onesCount x : ℝ) / n)
          (fun x _ => hp.nonneg x) hp.sum_eq_one fun x _ => by
            refine ⟨by positivity, ?_⟩
            rw [div_le_one hn']
            exact_mod_cast onesCount_le x
        simp only [smul_eq_mul] at hJ
        have hmean : ∑ x, iidPMF (bernoulliPMF θ) n x * ((onesCount x : ℝ) / n) = θ := by
          simp only [mul_div_assoc', ← sum_div, sum_iidPMF_mul_onesCount]
          field_simp
        rw [hmean] at hJ
        exact hJ
    _ = n * (binEntropy θ / log 2) + logb 2 (n + 1) + c := by ring

/-- **Theorem 14.3.1 (Relationship of Kolmogorov complexity and entropy), (14.27)–(14.28).** For
`n` Bernoulli(`θ`) trials, `(1/n) E K(Xⁿ | n) → H₀(θ)`. -/
theorem tendsto_expected_complexity_div {U : Computer} (hU : U.IsUniversal) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    Tendsto (fun n : ℕ => (∑ x : Fin n → Bool, iidPMF (bernoulliPMF θ) n x *
      U.complexity (List.ofFn x) n) / n) atTop (𝓝 (binEntropy θ / log 2)) := by
  obtain ⟨c, hc⟩ := expected_complexity_le hU
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hup : Tendsto (fun n : ℕ => binEntropy θ / log 2 + (logb 2 (n + 1) + c) / n) atTop
      (𝓝 (binEntropy θ / log 2)) := by
    have h := ((tendsto_log_add_one_div.div_const (log 2)).add
      (tendsto_const_div_atTop_nhds_zero_nat c))
    rw [zero_div, add_zero] at h
    have h' := tendsto_const_nhds (x := binEntropy θ / log 2) |>.add h
    rw [add_zero] at h'
    refine h'.congr fun n => ?_
    rw [logb, add_div, div_div, div_div, mul_comm (log 2)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := entropy_le_expected_complexity hU (iidPMF_isPMF (bernoulliPMF_isPMF h0 h1) n) n
    rw [entropyBase_eq_div, entropy_iidPMF (bernoulliPMF_isPMF h0 h1), entropy_bernoulliPMF] at h
    rw [le_div_iff₀ hn']
    calc binEntropy θ / log 2 * n = n * binEntropy θ / log 2 := by ring
      _ ≤ _ := h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    calc _ ≤ n * (binEntropy θ / log 2) + logb 2 (n + 1) + c := hc h0 h1 n
      _ = (binEntropy θ / log 2 + (logb 2 (n + 1) + c) / n) * n := by field_simp; ring

/-- **(14.36)–(14.37)** Without conditioning on the length, `(1/n) E K(Xⁿ) → H₀(θ)`. -/
theorem tendsto_expected_complexity_div' {U : Computer} (hU : U.IsUniversal) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    Tendsto (fun n : ℕ => (∑ x : Fin n → Bool, iidPMF (bernoulliPMF θ) n x *
      U.complexity (List.ofFn x) 0) / n) atTop (𝓝 (binEntropy θ / log 2)) := by
  obtain ⟨c, hc⟩ := expected_complexity_le hU
  obtain ⟨c', hc'⟩ := complexity_le_complexity_length_add hU
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hup : Tendsto (fun n : ℕ => binEntropy θ / log 2 + (3 * logb 2 (n + 1) + c + c') / n)
      atTop (𝓝 (binEntropy θ / log 2)) := by
    have h := (((tendsto_log_add_one_div.div_const (log 2)).const_mul 3).add
      (tendsto_const_div_atTop_nhds_zero_nat (c + c')))
    rw [zero_div, mul_zero, add_zero] at h
    have h' := tendsto_const_nhds (x := binEntropy θ / log 2) |>.add h
    rw [add_zero] at h'
    refine h'.congr fun n => ?_
    rw [logb]
    field_simp
    ring
  have hp := fun n => iidPMF_isPMF (bernoulliPMF_isPMF h0 h1) n
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := entropy_le_expected_complexity hU (hp n) 0
    rw [entropyBase_eq_div, entropy_iidPMF (bernoulliPMF_isPMF h0 h1), entropy_bernoulliPMF] at h
    rw [le_div_iff₀ hn']
    calc binEntropy θ / log 2 * n = n * binEntropy θ / log 2 := by ring
      _ ≤ _ := h
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have hK : ∀ x : Fin n → Bool, (U.complexity (List.ofFn x) 0 : ℝ) ≤
        U.complexity (List.ofFn x) n + 2 * logb 2 (n + 1) + c' := fun x => by
      simpa using hc' (List.ofFn x) 0
    calc ∑ x, iidPMF (bernoulliPMF θ) n x * U.complexity (List.ofFn x) 0
        ≤ ∑ x, iidPMF (bernoulliPMF θ) n x *
            (U.complexity (List.ofFn x) n + (2 * logb 2 (n + 1) + c')) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (by linarith [hK x]) ((hp n).nonneg x)
      _ = ∑ x, iidPMF (bernoulliPMF θ) n x * U.complexity (List.ofFn x) n +
            (2 * logb 2 (n + 1) + c') := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, (hp n).sum_eq_one, one_mul]
      _ ≤ n * (binEntropy θ / log 2) + logb 2 (n + 1) + c + (2 * logb 2 (n + 1) + c') := by
          linarith [hc h0 h1 n]
      _ = (binEntropy θ / log 2 + (3 * logb 2 (n + 1) + c + c') / n) * n := by
          field_simp
          ring

/-! ### Section 14.4: integers -/

/-- The binary string of the integer `n`: the digits of `n + 1` after the leading one. The map
`n ↦ natString n` is a bijection of `ℕ` onto the binary strings. -/
def natString (n : ℕ) : List Bool := lowBits (n + 1)

lemma natString_injective : Function.Injective natString := fun a b h => by
  have hl : Nat.log2 (a + 1) = Nat.log2 (b + 1) := by
    have := congrArg List.length h
    simpa [natString] using this
  exact Nat.succ_injective (eq_of_lowBits_eq (by omega) (by omega) hl h)

lemma length_natString (n : ℕ) : (natString n).length = Nat.log2 (n + 1) := by
  simp [natString]

/-- **(14.38)** The Kolmogorov complexity `K(n)` of an integer. -/
def Computer.natComplexity (U : Computer) (n : ℕ) : ℕ := U.complexity (natString n) 0

/-- **Theorem 14.4.1** `K_U(n) ≤ K_A(n) + c_A`. -/
theorem natComplexity_le_of_universal {U : Computer} (hU : U.IsUniversal) (A : Computer) :
    ∃ c, ∀ n, A.HasProgram (natString n) 0 → U.natComplexity n ≤ A.natComplexity n + c := by
  obtain ⟨c, hc⟩ := hU.complexity_le A
  exact ⟨c, fun n hn => hc _ _ hn⟩

/-- **Theorem 14.4.2, (14.20), (14.40)** `K(n) ≤ log₂ (n + 1) + 2 log₂ (log₂ (n + 1) + 1) + c`,
describing `n` by its binary digits preceded by a self-delimiting description of their number
(the book's `log* n` bound uses the recursive description). -/
theorem natComplexity_le {U : Computer} (hU : U.IsUniversal) :
    ∃ c : ℝ, ∀ n : ℕ, (U.natComplexity n : ℝ) ≤
      logb 2 (n + 1) + 2 * logb 2 (logb 2 (n + 1) + 1) + c := by
  obtain ⟨c, hc⟩ := complexity_le_length_add hU
  refine ⟨c, fun n => ?_⟩
  have h := hc (natString n) 0
  rw [length_natString] at h
  have h1 : (Nat.log2 (n + 1) : ℝ) ≤ logb 2 (n + 1) := by
    have := Real.log2_le_logb (n + 1)
    push_cast at this
    exact this
  have h2 : logb 2 ((Nat.log2 (n + 1) : ℝ) + 1) ≤ logb 2 (logb 2 (n + 1) + 1) :=
    logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  unfold Computer.natComplexity
  linarith

/-- **Theorem 14.4.3, (14.41)–(14.43).** There are infinitely many integers `n` with
`K(n) > log₂ n`: otherwise `∑ₙ 2^{-K(n)} ≥ ∑ₙ 1/n = ∞` would contradict the Kraft inequality. -/
theorem exists_natComplexity_gt {U : Computer} (hU : U.IsUniversal) (N : ℕ) :
    ∃ n ≥ N, logb 2 n < U.natComplexity n := by
  classical
  by_contra h
  push Not at h
  -- `∑_{N ≤ i < M} 1/(i + 1) ≤ ∑ 2^{-K(i + 1)} ≤ 1` for all `M`.
  have hbound : ∀ M, ∑ i ∈ (range M).filter (N ≤ ·), (1 / ((i : ℝ) + 1)) ≤ 1 := by
    intro M
    have hK := U.sum_two_pow_neg_complexity_le_one 0
      (((range M).filter (N ≤ ·)).image fun i => natString (i + 1))
      fun x _ => hU.hasProgram_all x 0
    rw [sum_image fun a _ b _ hab => Nat.succ_injective (natString_injective hab)] at hK
    refine le_trans (sum_le_sum fun i hi => ?_) hK
    have hNi : N ≤ i := (mem_filter.1 hi).2
    have hn' : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hK' := h (i + 1) (by omega)
    rw [Computer.natComplexity] at hK'
    push_cast at hK'
    have e1 : (1 / 2 : ℝ) ^ (U.complexity (natString (i + 1)) 0) =
        (2 : ℝ) ^ (-(U.complexity (natString (i + 1)) 0 : ℝ)) := by
      rw [rpow_neg (by norm_num), rpow_natCast, one_div, inv_pow]
    have e2 : 1 / ((i : ℝ) + 1) = (2 : ℝ) ^ (-logb 2 ((i : ℝ) + 1)) := by
      rw [rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn', one_div]
    simp only [Nat.succ_eq_add_one] at *
    rw [e1, e2]
    exact rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- The harmonic series diverges.
  obtain ⟨M, hM⟩ := (tendsto_atTop.1 Real.tendsto_sum_range_one_div_nat_succ_atTop (N + 2)).exists
  have hsplit := sum_filter_add_sum_filter_not (range M) (N ≤ ·) fun i => 1 / ((i : ℝ) + 1)
  have hrest : ∑ i ∈ (range M).filter (fun i => ¬N ≤ i), (1 / ((i : ℝ) + 1)) ≤ N := by
    calc ∑ i ∈ (range M).filter (fun i => ¬N ≤ i), (1 / ((i : ℝ) + 1))
        ≤ ∑ i ∈ (range M).filter (fun i => ¬N ≤ i), (1 : ℝ) := sum_le_sum fun i _ => by
          rw [div_le_one (by positivity)]
          linarith [i.cast_nonneg (α := ℝ)]
      _ = ((range M).filter (fun i => ¬N ≤ i)).card := by simp
      _ ≤ N := by
        have : (range M).filter (fun i => ¬N ≤ i) ⊆ range N := fun i hi => by
          simp only [mem_filter, not_le] at hi
          exact mem_range.2 hi.2
        exact_mod_cast (card_le_card this).trans (card_range N).le
  have := hbound M
  linarith

/-! ### Section 14.5: incompressible sequences -/

/-- **Theorem 14.5.1, (14.44)–(14.48).** For `n` fair coin flips,
`Pr{K(X₁ ⋯ Xₙ | n) < n - k} < 2^{-k}`. -/
theorem prob_complexity_lt_le {U : Computer} (hU : U.IsUniversal) {n k : ℕ} (hk : k ≤ n) :
    ∑ _x ∈ univ.filter (fun x : Fin n → Bool => U.complexity (List.ofFn x) n < n - k),
      (1 / 2 : ℝ) ^ n < (1 / 2 : ℝ) ^ k := by
  classical
  set F := univ.filter (fun x : Fin n → Bool => U.complexity (List.ofFn x) n < n - k)
  have hcard : (F.image List.ofFn).card < 2 ^ (n - k) :=
    U.card_lt_two_pow_of_complexity_lt _ fun w hw => by
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hw
      exact ⟨hU.hasProgram_all _ _, (mem_filter.1 hx).2⟩
  rw [card_image_of_injective _ injective_ofFn] at hcard
  rw [sum_const, nsmul_eq_mul]
  have : (F.card : ℝ) < 2 ^ (n - k) := by exact_mod_cast hcard
  calc (F.card : ℝ) * (1 / 2) ^ n < 2 ^ (n - k) * (1 / 2) ^ n :=
        mul_lt_mul_of_pos_right this (by positivity)
    _ = (1 / 2) ^ k := by
      have e : (1 / 2 : ℝ) ^ n = (1 / 2) ^ (n - k) * (1 / 2) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      rw [e, ← mul_assoc, ← mul_pow]
      norm_num

/-- **(14.49)–(14.50)** Every length has an algorithmically random string: some `xⁿ` has
`K(xⁿ | n) ≥ n`. -/
theorem exists_random {U : Computer} (hU : U.IsUniversal) (n : ℕ) :
    ∃ x : Fin n → Bool, n ≤ U.complexity (List.ofFn x) n := by
  classical
  by_contra h
  push Not at h
  have := U.card_lt_two_pow_of_complexity_lt (k := n) (y := n) (univ.image List.ofFn)
    fun w hw => by
      obtain ⟨x, -, rfl⟩ := mem_image.1 hw
      exact ⟨hU.hasProgram_all _ _, h x⟩
  rw [card_image_of_injective _ injective_ofFn] at this
  simp at this

/-- The first `n` bits of an infinite binary sequence. -/
abbrev prefixBits (x : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn fun i : Fin n => x i

/-- **(14.51)** An infinite binary sequence is incompressible if `K(x₁ ⋯ xₙ | n)/n → 1`. -/
def IsIncompressible (U : Computer) (x : ℕ → Bool) : Prop :=
  Tendsto (fun n : ℕ => (U.complexity (prefixBits x n) n : ℝ) / n) atTop (𝓝 1)

/-- `2 (p - ½)² ≤ log 2 - H(p)` (Pinsker's inequality for `Bernoulli(p)` against
`Bernoulli(½)`). -/
lemma two_mul_sq_le_log_two_sub {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    2 * (p - 1 / 2) ^ 2 ≤ log 2 - binEntropy p := by
  have h := two_mul_sq_le_binary h0 h1 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have e : p * log (p / (1 / 2)) + (1 - p) * log ((1 - p) / (1 - 1 / 2)) =
      log 2 - binEntropy p := by
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, negMulLog, negMulLog]
    rcases h0.eq_or_lt with rfl | hp0
    · norm_num
    rcases h1.eq_or_lt with rfl | hp1
    · norm_num
    have hq : 0 < 1 - p := by linarith
    rw [show p / (1 / 2) = 2 * p by ring, show (1 - p) / (1 - 1 / 2) = 2 * (1 - p) by ring,
      log_mul (by norm_num) hp0.ne', log_mul (by norm_num) hq.ne']
    ring
  linarith

/-- **Theorem 14.5.2 (Strong law of large numbers for incompressible sequences), (14.52)–(14.57).**
The proportion of ones in an incompressible sequence tends to `½`. -/
theorem IsIncompressible.tendsto_ones_div {U : Computer} (hU : U.IsUniversal) {x : ℕ → Bool}
    (hx : IsIncompressible U x) :
    Tendsto (fun n : ℕ => (ones (prefixBits x n) : ℝ) / n) atTop (𝓝 (1 / 2)) := by
  obtain ⟨c, hc⟩ := complexity_le_binEntropy hU
  have hl : 0 < log 2 := log_pos (by norm_num)
  set θ := fun n : ℕ => (ones (prefixBits x n) : ℝ) / n
  have hθ : ∀ n, 0 ≤ θ n ∧ θ n ≤ 1 := fun n => by
    refine ⟨by positivity, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [θ]
    · rw [div_le_one (by exact_mod_cast hn)]
      have := ones_le_length (prefixBits x n)
      simp only [List.length_ofFn] at this
      exact_mod_cast this
  -- `1 - H₀(θₙ) ≤ 1 - K/n + (log₂ (n + 1) + c)/n → 0`.
  have hgap : Tendsto (fun n : ℕ => 1 - (U.complexity (prefixBits x n) n : ℝ) / n +
      (logb 2 (n + 1) + c) / n) atTop (𝓝 0) := by
    have h := ((tendsto_log_add_one_div.div_const (log 2)).add
      (tendsto_const_div_atTop_nhds_zero_nat c))
    rw [zero_div, add_zero] at h
    have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub hx |>.add h
    rw [sub_self, add_zero] at h'
    refine h'.congr fun n => ?_
    rw [logb, add_div, div_div, div_div, mul_comm (log 2)]
  have hsq : Tendsto (fun n : ℕ => 2 * (θ n - 1 / 2) ^ 2) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hgap.const_mul (log 2) |>.trans_eq (by rw [mul_zero])) ?_ ?_
    · exact Eventually.of_forall fun n => by positivity
    · filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 := two_mul_sq_le_log_two_sub (hθ n).1 (hθ n).2
      have h2 := hc (prefixBits x n)
      simp only [List.length_ofFn] at h2
      have h3 : (U.complexity (prefixBits x n) n : ℝ) / n ≤
          binEntropy (θ n) / log 2 + (logb 2 (n + 1) + c) / n := by
        rw [div_le_iff₀ hn']
        calc (U.complexity (prefixBits x n) n : ℝ) ≤ n * (binEntropy (θ n) / log 2) +
            logb 2 (n + 1) + c := h2
          _ = (binEntropy (θ n) / log 2 + (logb 2 (n + 1) + c) / n) * n := by field_simp; ring
      have h4 : log 2 - binEntropy (θ n) ≤ log 2 * (1 - (U.complexity (prefixBits x n) n : ℝ) / n +
          (logb 2 (n + 1) + c) / n) := by
        have : binEntropy (θ n) / log 2 * log 2 = binEntropy (θ n) := div_mul_cancel₀ _ hl.ne'
        nlinarith
      linarith
  have hsq' : Tendsto (fun n : ℕ => (θ n - 1 / 2) ^ 2) atTop (𝓝 0) := by
    have := hsq.const_mul (1 / 2)
    simpa [← mul_assoc] using this
  have habs : Tendsto (fun n : ℕ => |θ n - 1 / 2|) atTop (𝓝 0) := by
    have := (continuous_sqrt.tendsto 0).comp hsq'
    simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at this
    exact this
  have := ((tendsto_zero_iff_abs_tendsto_zero _).2 habs).add_const (1 / 2)
  simp only [sub_add_cancel, zero_add] at this
  exact this

/-! ### Theorem 14.5.3 -/

/-- The upper tail: `Pr{K(Xⁿ | n)/n ≥ H₀(θ) + ε} → 0`, by Theorem 14.2.5 and the weak law. -/
lemma tendsto_prob_complexity_ge {U : Computer} (hU : U.IsUniversal) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF (bernoulliPMF θ) n) (univ.filter fun x : Fin n → Bool =>
      binEntropy θ / log 2 + ε ≤ (U.complexity (List.ofFn x) n : ℝ) / n)) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := complexity_le_binEntropy hU
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hq := bernoulliPMF_isPMF h0 h1
  -- Continuity of `H₀` at `θ`.
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 binEntropy_continuous θ (ε * log 2 / 2)
    (div_pos (mul_pos hε hl) two_pos)
  -- The weak law for the proportion of ones.
  have hwl := weak_law hq (fun b => if b then (1 : ℝ) else 0) δ hδ
  have hmean : expect (bernoulliPMF θ) (fun b => if b then (1 : ℝ) else 0) = θ := by
    simp [expect, bernoulliPMF]
  rw [hmean] at hwl
  -- For `n` large, the error terms are below `ε / 2`.
  have hsmall : ∀ᶠ n : ℕ in atTop, (logb 2 (n + 1) + c) / n < ε / 2 := by
    have h := (tendsto_log_add_one_div.div_const (log 2)).add
      (tendsto_const_div_atTop_nhds_zero_nat c)
    rw [zero_div, add_zero] at h
    refine ((tendsto_order.1 h).2 (ε / 2) (by positivity)).mono fun n hn => ?_
    rw [show (logb 2 (↑n + 1) + c) / ↑n = log (↑n + 1) / ↑n / log 2 + c / ↑n by
      rw [logb, add_div, div_div, div_div, mul_comm (log 2)]]
    exact hn
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hwl
    (Eventually.of_forall fun n => prob_nonneg (iidPMF_isPMF hq n).nonneg _) ?_
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  refine prob_mono (iidPMF_isPMF hq n).nonneg fun x hx => ?_
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  -- Otherwise `H₀(x̄) < H₀(θ) + ε/2`, and `K/n < H₀(θ) + ε`.
  by_contra hlt
  push Not at hlt
  have hmean' : sampleMean (fun i => (fun b : Bool => if b then (1 : ℝ) else 0) (x i)) =
      onesCount x / n := by
    simp [sampleMean, onesCount]
  rw [hmean'] at hlt
  have hH := hcont (onesCount x / n) (by rw [Real.dist_eq]; exact hlt)
  rw [Real.dist_eq] at hH
  have hK := hc (List.ofFn x)
  simp only [List.length_ofFn, ones_ofFn] at hK
  have h2 : (U.complexity (List.ofFn x) n : ℝ) / n ≤
      binEntropy (onesCount x / n) / log 2 + (logb 2 (n + 1) + c) / n := by
    rw [div_le_iff₀ hn']
    calc (U.complexity (List.ofFn x) n : ℝ) ≤ n * (binEntropy (onesCount x / n) / log 2) +
        logb 2 (n + 1) + c := hK
      _ = _ := by field_simp; ring
  have h3 : binEntropy (onesCount x / n) / log 2 < binEntropy θ / log 2 + ε / 2 := by
    rw [div_lt_iff₀ hl]
    have : (binEntropy θ / log 2 + ε / 2) * log 2 = binEntropy θ + ε * log 2 / 2 := by
      field_simp
    rw [this]
    linarith [le_abs_self (binEntropy (onesCount x / n) - binEntropy θ)]
  linarith

/-- The lower tail: `Pr{K(Xⁿ | n)/n ≤ H₀(θ) - ε} → 0`: there are fewer than
`2^{n (H₀(θ) - ε) + 1}` such strings, and by the AEP the typical strings have probability at most
`2^{-n (H₀(θ) - ε/2)}`. -/
lemma tendsto_prob_complexity_le {U : Computer} (hU : U.IsUniversal) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => prob (iidPMF (bernoulliPMF θ) n) (univ.filter fun x : Fin n → Bool =>
      (U.complexity (List.ofFn x) n : ℝ) / n ≤ binEntropy θ / log 2 - ε)) atTop (𝓝 0) := by
  classical
  have hl : 0 < log 2 := log_pos (by norm_num)
  have hq := bernoulliPMF_isPMF h0 h1
  set H := binEntropy θ
  rcases lt_or_ge (H / log 2 - ε) 0 with hneg | hpos
  · -- No string has negative complexity.
    refine tendsto_const_nhds.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
    have : (univ.filter fun x : Fin n → Bool =>
        (U.complexity (List.ofFn x) n : ℝ) / n ≤ H / log 2 - ε) = ∅ := by
      refine filter_eq_empty_iff.2 fun x _ => ?_
      have : (0 : ℝ) ≤ (U.complexity (List.ofFn x) n : ℝ) / n := by positivity
      linarith
    dsimp only
    rw [this]
    simp [prob]
  set η := ε * log 2 / 2
  have hη : 0 < η := by positivity
  have haep := aep hq η hη
  rw [entropy_bernoulliPMF] at haep
  have hexp : Tendsto (fun n : ℕ => 2 * exp (-(η * n))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hη)).const_mul 2
    rw [mul_zero] at this
    exact this
  have hsum := (haep.add hexp)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => prob_nonneg (iidPMF_isPMF hq n).nonneg _) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hp := iidPMF_isPMF hq n
  set p := iidPMF (bernoulliPMF θ) n
  set L := univ.filter fun x : Fin n → Bool =>
    (U.complexity (List.ofFn x) n : ℝ) / n ≤ H / log 2 - ε
  set A := univ.filter fun x : Fin n → Bool => η ≤ |sampleEntropy (bernoulliPMF θ) x - H|
  -- Split `L` into its atypical and typical parts.
  have hLA : prob p L ≤ prob p A + prob p (L.filter fun x => x ∉ A) := by
    refine (prob_mono hp.nonneg fun x hx => ?_).trans (prob_union_le hp.nonneg _ _)
    by_cases hxA : x ∈ A
    · exact mem_union_left _ hxA
    · exact mem_union_right _ (mem_filter.2 ⟨hx, hxA⟩)
  -- The typical strings have probability at most `e^{-n (H - η)}`.
  have hptyp : ∀ x ∈ L.filter (fun x => x ∉ A), p x ≤ exp (-(n * (H - η))) := fun x hx => by
    have hxA := (mem_filter.1 hx).2
    simp only [A, mem_filter, mem_univ, true_and, not_le] at hxA
    rcases (hp.nonneg x).eq_or_lt with h | h
    · rw [← h]; exact (exp_pos _).le
    have hs : H - η < sampleEntropy (bernoulliPMF θ) x := by
      linarith [neg_abs_le (sampleEntropy (bernoulliPMF θ) x - H)]
    rw [sampleEntropy, lt_div_iff₀ hn'] at hs
    rw [← exp_log h]
    exact exp_le_exp.2 (by nlinarith)
  -- Fewer than `2ᵐ` strings have complexity at most `n (H₀ - ε)`, `m = ⌊n (H₀ - ε)⌋ + 1`.
  set y := n * (H / log 2 - ε)
  have hy : 0 ≤ y := by positivity
  set m := ⌊y⌋₊ + 1
  have hcard : L.card < 2 ^ m := by
    have h := U.card_lt_two_pow_of_complexity_lt (y := n) (k := m) (L.image List.ofFn)
      fun w hw => by
        obtain ⟨x, hx, rfl⟩ := mem_image.1 hw
        refine ⟨hU.hasProgram_all _ _, ?_⟩
        have hx' := (mem_filter.1 hx).2
        rw [div_le_iff₀ hn'] at hx'
        have : (U.complexity (List.ofFn x) n : ℝ) < m := by
          have := Nat.lt_floor_add_one y
          push_cast [m]
          nlinarith
        exact_mod_cast this
    rwa [card_image_of_injective _ injective_ofFn] at h
  have hpow : ((2 : ℕ) ^ m : ℝ) ≤ 2 * exp (n * (H - ε * log 2)) := by
    have h1 : ((2 : ℕ) ^ m : ℝ) = 2 * (2 : ℝ) ^ (⌊y⌋₊ : ℝ) := by
      push_cast [m]
      rw [pow_succ, rpow_natCast]
      ring
    have h2 : (2 : ℝ) ^ (⌊y⌋₊ : ℝ) ≤ (2 : ℝ) ^ y :=
      rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hy)
    have h3 : (2 : ℝ) ^ y = exp (n * (H - ε * log 2)) := by
      rw [rpow_def_of_pos (by norm_num)]
      congr 1
      simp only [y]
      field_simp
    rw [h1]
    linarith
  have htyp : prob p (L.filter fun x => x ∉ A) ≤ 2 * exp (-(η * n)) := by
    calc prob p (L.filter fun x => x ∉ A) ≤ ∑ x ∈ L.filter (fun x => x ∉ A), exp (-(n * (H - η)))
          := sum_le_sum hptyp
      _ ≤ L.card * exp (-(n * (H - η))) := by
          rw [sum_const, nsmul_eq_mul]
          gcongr
          exact filter_subset _ _
      _ ≤ 2 * exp (n * (H - ε * log 2)) * exp (-(n * (H - η))) := by
          gcongr
          exact (by exact_mod_cast hcard.le : (L.card : ℝ) ≤ ((2 : ℕ) ^ m : ℝ)).trans hpow
      _ = 2 * exp (-(η * n)) := by
          rw [mul_assoc, ← exp_add]
          congr 2
          simp only [η]
          ring
  linarith

/-- **Theorem 14.5.3, (14.58)–(14.65).** For `n` Bernoulli(`θ`) trials, the complexity per symbol
converges to the entropy in probability: `(1/n) K(X₁ ⋯ Xₙ | n) → H₀(θ)`. -/
theorem tendstoInProb_complexity_div {U : Computer} (hU : U.IsUniversal) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    TendstoInProb (fun n => iidPMF (bernoulliPMF θ) n)
      (fun n x => (U.complexity (List.ofFn x) n : ℝ) / n) (binEntropy θ / log 2) := by
  classical
  intro ε hε
  have hq := bernoulliPMF_isPMF h0 h1
  have hsum := (tendsto_prob_complexity_ge hU h0 h1 hε).add (tendsto_prob_complexity_le hU h0 h1 hε)
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => prob_nonneg (iidPMF_isPMF hq n).nonneg _)
    (Eventually.of_forall fun n => ?_)
  refine (prob_mono (iidPMF_isPMF hq n).nonneg fun x hx => ?_).trans
    (prob_union_le (iidPMF_isPMF hq n).nonneg _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union] at hx ⊢
  rcases le_abs'.1 hx with h | h
  · right; linarith
  · left; linarith

end InfoTheory
