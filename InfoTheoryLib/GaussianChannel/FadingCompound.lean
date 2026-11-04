/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.GaussianChannel.AWGN
public import InfoTheoryLib.Network.Gaussian

/-!
# The slowly fading Gaussian channel: the compound channel approach

Consider the Gaussian channel `Y = gX + Z` with a gain `g` in a finite set, known to the decoder and
constant over the block. Coding against the worst gain gives the compound capacity `min_g C(g²P)`,
and it does not change if the encoder also knows the gain.

The converse is that of the AWGN channel for the worst gain. For achievability, a code for the worst
gain `g₀` works for a gain `|g| ≥ |g₀|`: the decoder knows `g`, multiplies the output by `a = g₀/g`
and adds Gaussian noise of variance `1 - a²`, so that it sees the channel with gain `g₀`. This
randomized decoder can be replaced by a deterministic one, as the probability of error averaged over
the added noise is that of the code for `g₀`.

## Main definitions

* `IsAchievableFadingCompound g P R`, `fadingCompoundCapacity g P`: achievable rates in bits and the
  capacity, with one encoder and a decoder for each gain.
* `IsAchievableFadingCompoundE g P R`, `fadingCompoundCapacityE g P`: the same with an encoder for
  each gain.
* `fadingCompoundValue g P`: `min_g C(g²P)`.

## Main statements

* `map_noiseLaw_prod`: `a Zⁿ + Vⁿ ∼ N(0, 1)ⁿ` for independent `Zⁿ ∼ N(0, 1)ⁿ`, `Vⁿ ∼ N(0, 1 - a²)ⁿ`.
* `GaussianCode.exists_dec_degraded`: a code for the gain `g₀` is a code for a larger gain.
* `fadingCompoundCapacity_eq`, `fadingCompoundCapacityE_eq`: the capacities are `min_g C(g²P)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 8
-/

open Real MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace InfoTheory

open GaussianCode

/-! ### Degrading the channel -/

/-- `a Z + V ∼ N(0, 1)` for independent `Z ∼ N(0, 1)` and `V ∼ N(0, N)` with `a² + N = 1`. -/
lemma map_gaussianReal_prod {a : ℝ} {N : ℝ≥0} (h : a ^ 2 + N = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 N)).map (fun p : ℝ × ℝ => a * p.1 + p.2) =
      gaussianReal 0 1 := by
  set v₁ : ℝ≥0 := ⟨a ^ 2, sq_nonneg a⟩ with hv₁
  have e1 : (gaussianReal 0 1).map (a * ·) = gaussianReal 0 v₁ := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    rfl
  have hv : v₁ + N = 1 := by
    apply NNReal.eq
    rw [NNReal.coe_add, NNReal.coe_one]
    exact h
  have hc := gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0) (v₁ := v₁) (v₂ := N)
  rw [hv, add_zero] at hc
  have hp := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 N)
    (measurable_const_mul a) measurable_id
  rw [Measure.map_id] at hp
  refine Eq.trans ?_ hc
  rw [← e1, Measure.conv, hp, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- `a Zⁿ + Vⁿ ∼ N(0, 1)ⁿ` for independent `Zⁿ ∼ N(0, 1)ⁿ` and `Vⁿ ∼ N(0, N)ⁿ` with `a² + N = 1`. -/
theorem map_noiseLaw_prod {a : ℝ} {N : ℝ≥0} (h : a ^ 2 + N = 1) (n : ℕ) :
    ((noiseLaw 1 n).prod (noiseLaw N n)).map (fun p => fun i => a * p.1 i + p.2 i) =
      noiseLaw 1 n := by
  have hpres := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n)
    (fun _ => gaussianReal 0 1) (fun _ => gaussianReal 0 N)
  rw [noiseLaw, noiseLaw, ← hpres.map_eq, Measure.map_map (by fun_prop)
    hpres.measurable]
  have hf : ∀ _ : Fin n, AEMeasurable (fun p : ℝ × ℝ => a * p.1 + p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 N)) := fun _ => by fun_prop
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin n => (gaussianReal 0 1).prod (gaussianReal 0 N))
    (f := fun _ (p : ℝ × ℝ) => a * p.1 + p.2) hf
  simp only [map_gaussianReal_prod h] at hpi
  exact hpi

namespace GaussianCode

variable {M n : ℕ}

/-- **Degradedness of the Gaussian channel in the gain.** A code for the gain `g₀` is a code for a
gain `g` with `g₀² ≤ g²`, with the same codewords and a suitable decoder: `yⁿ ↦ a yⁿ + vⁿ` turns the
channel into the one with gain `g₀` when `vⁿ` is drawn from `N(0, 1 - a²)ⁿ`, and some `vⁿ` is at
least as good as the average. -/
theorem exists_dec_degraded (c : GaussianCode M n) {g₀ g : ℝ} (hg : g ≠ 0) (h : g₀ ^ 2 ≤ g ^ 2) :
    ∃ (d : (Fin n → ℝ) → Fin M) (hd : Measurable d),
      ((⟨c.enc, d, hd⟩ : GaussianCode M n).scale g).avgErrProb 1 ≤ (c.scale g₀).avgErrProb 1 := by
  classical
  set a := g₀ / g with ha
  have hg2 : 0 < g ^ 2 := by positivity
  have ha2 : a ^ 2 ≤ 1 := by
    rw [ha, div_pow, div_le_one hg2]
    exact h
  set N : ℝ≥0 := ⟨1 - a ^ 2, by linarith⟩
  have hN : a ^ 2 + (N : ℝ) = 1 := by
    change a ^ 2 + (1 - a ^ 2) = 1
    ring
  have hmap := map_noiseLaw_prod hN n
  set μ := noiseLaw 1 n
  set ν := noiseLaw N n
  set T : (Fin n → ℝ) × (Fin n → ℝ) → Fin n → ℝ := fun p i => a * p.1 i + p.2 i
  have hT : Measurable T := by fun_prop
  set S : Fin M → Set (Fin n → ℝ) := fun w => {u | c.dec (g₀ • c.enc w + u) ≠ w}
  have hS : ∀ w, MeasurableSet (S w) := fun w => by
    have hm : Measurable fun u : Fin n → ℝ => c.dec (g₀ • c.enc w + u) :=
      c.measurable_dec.comp (by fun_prop)
    exact (hm (measurableSet_singleton w)).compl
  have hsec : ∀ w, μ (S w) = ∫⁻ v, μ ((fun z => (z, v)) ⁻¹' (T ⁻¹' S w)) ∂ν := fun w => by
    rw [← Measure.prod_apply_symm (hT (hS w)), ← Measure.map_apply hT (hS w), hmap]
  set f : (Fin n → ℝ) → ℝ≥0∞ := fun v => ∑ w, μ ((fun z => (z, v)) ⁻¹' (T ⁻¹' S w))
  have hfm : Measurable f := Finset.measurable_sum _ fun w _ =>
    measurable_measure_prodMk_right (hT (hS w))
  have hint : ∫⁻ v, f v ∂ν = ∑ w, μ (S w) := by
    rw [lintegral_finsetSum _ fun w _ => measurable_measure_prodMk_right (hT (hS w))]
    exact sum_congr rfl fun w _ => (hsec w).symm
  obtain ⟨v, hv⟩ := exists_le_lintegral hfm.aemeasurable (μ := ν)
  rw [hint] at hv
  refine ⟨fun y => c.dec fun i => a * y i + v i, c.measurable_dec.comp (by fun_prop), ?_⟩
  have hset : ∀ w, {z | c.dec (fun i => a * ((g • c.enc w + z) i) + v i) ≠ w} =
      (fun z => (z, v)) ⁻¹' (T ⁻¹' S w) := fun w => by
    ext z
    have e : (fun i => a * ((g • c.enc w + z) i) + v i) = g₀ • c.enc w + T (z, v) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, T, ha]
      field_simp
      ring
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, S, e]
  simp only [avgErrProb, condErrProb]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg M)
  have hne : ∑ w, μ (S w) ≠ ∞ := ENNReal.sum_ne_top.2 fun w _ => measure_ne_top _ _
  have hfin : ∀ w, μ ((fun z => (z, v)) ⁻¹' (T ⁻¹' S w)) ≠ ∞ := fun w => measure_ne_top _ _
  have h1 : ∑ w, (noiseLaw 1 n).real {z | ((⟨c.enc, fun y => c.dec fun i => a * y i + v i,
      c.measurable_dec.comp (by fun_prop)⟩ : GaussianCode M n).scale g).dec
        (((⟨c.enc, fun y => c.dec fun i => a * y i + v i,
          c.measurable_dec.comp (by fun_prop)⟩ : GaussianCode M n).scale g).enc w + z) ≠ w} =
      (f v).toReal := by
    rw [ENNReal.toReal_sum fun w _ => hfin w]
    refine sum_congr rfl fun w _ => ?_
    exact congrArg (fun A => (μ A).toReal) (hset w)
  rw [h1]
  have h2 : ∑ w, (noiseLaw 1 n).real {z | (c.scale g₀).dec ((c.scale g₀).enc w + z) ≠ w} =
      (∑ w, μ (S w)).toReal := by
    rw [ENNReal.toReal_sum fun w _ => measure_ne_top _ _]
    rfl
  rw [h2]
  exact ENNReal.toReal_mono hne hv

end GaussianCode

/-! ### The compound capacity -/

variable {𝒢 : Type*} [Fintype 𝒢] [Nonempty 𝒢]

/-- The probability of error `max_g P{M ≠ M̂ | g}` of a family of codes for the gains. -/
def fadingCompoundErr {M n : ℕ} (g : 𝒢 → ℝ) (c : 𝒢 → GaussianCode M n) : ℝ :=
  univ.sup' univ_nonempty fun s => ((c s).scale (g s)).avgErrProb 1

/-- **Lecture 8 of [elgamal2010].** A rate `R`, in bits, is achievable for the slowly fading
Gaussian channel with the gain at the decoder only, with the compound channel approach: the codes
for the gains have the same encoder, which satisfies the power constraint, and the probability of
error for the worst gain tends to `0`. -/
def IsAchievableFadingCompound (g : 𝒢 → ℝ) (P : ℝ≥0) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, 𝒢 → GaussianCode (2 ^ ⌈n * R⌉₊) n, (∀ n s s', (c n s).enc = (c n s').enc) ∧
    (∀ n s, (c n s).SatisfiesPower P) ∧ Tendsto (fun n => fadingCompoundErr g (c n)) atTop (𝓝 0)

/-- The capacity with the gain at the decoder only, in bits. -/
def fadingCompoundCapacity (g : 𝒢 → ℝ) (P : ℝ≥0) : ℝ := sSup {R | IsAchievableFadingCompound g P R}

/-- A rate `R`, in bits, is achievable with the gain at both the encoder and the decoder: there is a
code for each gain. -/
def IsAchievableFadingCompoundE (g : 𝒢 → ℝ) (P : ℝ≥0) (R : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, 𝒢 → GaussianCode (2 ^ ⌈n * R⌉₊) n, (∀ n s, (c n s).SatisfiesPower P) ∧
    Tendsto (fun n => fadingCompoundErr g (c n)) atTop (𝓝 0)

/-- The capacity with the gain at both the encoder and the decoder, in bits. -/
def fadingCompoundCapacityE (g : 𝒢 → ℝ) (P : ℝ≥0) : ℝ :=
  sSup {R | IsAchievableFadingCompoundE g P R}

/-- **Lecture 8 of [elgamal2010], page 8-8.** `C_CC = min_g C(g²P)`, in nats. -/
def fadingCompoundValue (g : 𝒢 → ℝ) (P : ℝ) : ℝ :=
  univ.inf' univ_nonempty fun s => gaussCap (g s ^ 2 * P)

lemma IsAchievableFadingCompound.isAchievableE {g : 𝒢 → ℝ} {P : ℝ≥0} {R : ℝ}
    (h : IsAchievableFadingCompound g P R) : IsAchievableFadingCompoundE g P R := by
  obtain ⟨c, -, hp, hl⟩ := h
  exact ⟨c, hp, hl⟩

/-- The converse: a rate that is achievable is at most `min_g C(g²P)`, by the AWGN channel with the
worst gain. -/
theorem IsAchievableFadingCompoundE.le {g : 𝒢 → ℝ} {P : ℝ≥0} {R : ℝ}
    (h : IsAchievableFadingCompoundE g P R) : R ≤ fadingCompoundValue g P / log 2 := by
  obtain ⟨c, hp, hl⟩ := h
  obtain ⟨s, -, hs⟩ := exists_mem_eq_inf' (s := (univ : Finset 𝒢)) univ_nonempty
    fun s => gaussCap (g s ^ 2 * P)
  have hA : IsAchievableAWGNRate (g s) P R := by
    refine ⟨fun n => c n s, fun n => hp n s, ?_⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun n => avgErrProb_nonneg _ _) fun n => ?_
    exact le_sup' (fun s => ((c n s).scale (g s)).avgErrProb 1) (mem_univ s)
  have := hA.le
  rw [fadingCompoundValue, hs]
  exact this

/-- Achievability: the code for the worst gain, with a decoder for each gain. -/
theorem isAchievableFadingCompound_of_lt {g : 𝒢 → ℝ} (hg : ∀ s, g s ≠ 0) {P : ℝ≥0} {R : ℝ}
    (hR : R < fadingCompoundValue g P / log 2) : IsAchievableFadingCompound g P R := by
  obtain ⟨s₀, -, hs₀⟩ := exists_min_image (univ : Finset 𝒢) (fun s => g s ^ 2) univ_nonempty
  have hle : fadingCompoundValue g P ≤ gaussCap (g s₀ ^ 2 * P) :=
    inf'_le (fun s => gaussCap (g s ^ 2 * P)) (mem_univ s₀)
  have hR' : R < gaussianCapacityFun (g s₀ ^ 2 * P) / log 2 :=
    hR.trans_le (div_le_div_of_nonneg_right hle (log_pos one_lt_two).le)
  obtain ⟨c, hp, hl⟩ := isAchievableAWGNRate_of_lt (hg s₀) hR'
  choose d hd hdb using fun (n : ℕ) (s : 𝒢) =>
    (c n).exists_dec_degraded (hg s) (hs₀ s (mem_univ s))
  refine ⟨fun n s => ⟨(c n).enc, d n s, hd n s⟩, fun _ _ _ => rfl, fun n _ => hp n, ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun n => ?_) fun n => ?_
  · exact (avgErrProb_nonneg _ _).trans
      (le_sup' (fun s => ((⟨(c n).enc, d n s, hd n s⟩ : GaussianCode _ n).scale (g s)).avgErrProb 1)
        (mem_univ s₀))
  · exact sup'_le _ _ fun s _ => hdb n s

/-- If all the rates below `C` are in `A` and all the rates in `A` are at most `C`, `sSup A = C`. -/
lemma sSup_eq_of_forall_mem' {A : Set ℝ} {C : ℝ} (h₁ : ∀ R ∈ A, R ≤ C) (h₂ : ∀ R < C, R ∈ A) :
    sSup A = C :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨C - 1, h₂ _ (by linarith)⟩ h₁ fun R hR =>
    ⟨(R + C) / 2, h₂ _ (by linarith), by linarith⟩

/-- **Lecture 8 of [elgamal2010], page 8-8.** With the gain at the decoder only, the compound
channel approach gives the capacity `C_CC = min_g C(g²P)`, in bits. -/
theorem fadingCompoundCapacity_eq {g : 𝒢 → ℝ} (hg : ∀ s, g s ≠ 0) (P : ℝ≥0) :
    fadingCompoundCapacity g P = fadingCompoundValue g P / log 2 :=
  sSup_eq_of_forall_mem' (fun _ h => (IsAchievableFadingCompound.isAchievableE h).le)
    fun _ hR => isAchievableFadingCompound_of_lt hg hR

/-- **Lecture 8 of [elgamal2010], page 8-10.** With the gain at both the encoder and the decoder,
the compound channel approach gives the same capacity `C_CC-E = min_g C(g²P) = C_CC`, in bits. -/
theorem fadingCompoundCapacityE_eq {g : 𝒢 → ℝ} (hg : ∀ s, g s ≠ 0) (P : ℝ≥0) :
    fadingCompoundCapacityE g P = fadingCompoundValue g P / log 2 :=
  sSup_eq_of_forall_mem' (fun _ h => IsAchievableFadingCompoundE.le h)
    fun _ hR => (isAchievableFadingCompound_of_lt hg hR).isAchievableE

end InfoTheory
