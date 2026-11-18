/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Theorem
public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.MarkovChain.DataProcessing

/-!
# Source–channel separation with distortion

An i.i.d. source `V₁, …, Vₙ ∼ p(v)` is encoded as `n` inputs `Xⁿ(Vⁿ)` of a discrete memoryless
channel of capacity `C`, and the output `Yⁿ` is mapped to a reproduction `V̂ⁿ = g(Yⁿ)`. The
distortion `D` is achievable by such schemes if `R(D) < C`, and only if `R(D) ≤ C`: a rate
distortion code followed by a channel code is as good as any joint scheme.

## Main definitions

* `LossySourceChannelCode n 𝒱 𝒱' α β`: a joint source–channel code with reproduction alphabet `𝒱'`.
* `LossySourceChannelCode.distortion`: its expected distortion `E d(Vⁿ, V̂ⁿ)`.
* `IsAchievableSCDistortion`: achievability of a distortion by joint source–channel codes.

## Main statements

* `LossySourceChannelCode.infoRD_le_capacity`: `R(E d(Vⁿ, V̂ⁿ)) ≤ C` for every code.
* `IsAchievableSCDistortion.infoRD_le_capacity`: **Theorem 10.4.1 (converse)**.
* `isAchievableSCDistortion_of_infoRD_lt`: **Theorem 10.4.1 (achievability)**.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Theorem 10.4.1 and
  Problem 10.17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒱 𝒱' α β : Type*} [Fintype 𝒱] [Fintype 𝒱'] [Fintype α] [Fintype β]

/-- **Theorem 10.4.1.** A joint source–channel code of block length `n`: an encoder mapping a
source block `vⁿ` to a channel codeword `xⁿ(vⁿ)`, and a decoder mapping the output `yⁿ` to a
reproduction `v̂ⁿ = g(yⁿ)`. -/
structure LossySourceChannelCode (n : ℕ) (𝒱 𝒱' α β : Type*) where
  /-- The encoder `vⁿ ↦ xⁿ(vⁿ)`. -/
  enc : (Fin n → 𝒱) → Fin n → α
  /-- The decoder `g : 𝒴ⁿ → 𝒱̂ⁿ`. -/
  dec : (Fin n → β) → Fin n → 𝒱'

/-- **Theorem 10.4.1.** The distortion `D = E d(Vⁿ, V̂ⁿ)` of a joint source–channel code for an
i.i.d. source `p` and a channel `W` used without feedback. -/
def LossySourceChannelCode.distortion {n : ℕ} (p : 𝒱 → ℝ) (W : α → β → ℝ) (d : 𝒱 → 𝒱' → ℝ)
    (c : LossySourceChannelCode n 𝒱 𝒱' α β) : ℝ :=
  ∑ v, ∑ y, iidPMF p n v * channelExt W n (c.enc v) y * seqDistortion d v (c.dec y)

/-- **Theorem 10.4.1.** A distortion `D` is achievable over the channel `W` if there are joint
source–channel codes with `limsup E d(Vⁿ, V̂ⁿ) ≤ D`. -/
def IsAchievableSCDistortion (p : 𝒱 → ℝ) (W : α → β → ℝ) (d : 𝒱 → 𝒱' → ℝ) (D : ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, LossySourceChannelCode n 𝒱 𝒱' α β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion p W d ≤ D + ε

variable {p : 𝒱 → ℝ} {W : α → β → ℝ} {d : 𝒱 → 𝒱' → ℝ}

/-! ### The converse -/

/-- **Theorem 10.4.1 (converse), for one code.** Every joint source–channel code has
`R(E d(Vⁿ, V̂ⁿ)) ≤ C`: `n R(D) ≤ I(Vⁿ; V̂ⁿ) ≤ I(Vⁿ; Yⁿ) ≤ nC`. -/
theorem LossySourceChannelCode.infoRD_le_capacity [Nonempty α] [Nonempty 𝒱'] (hp : IsPMF p)
    (hW : IsChannel W) {n : ℕ} (hn : 0 < n) (c : LossySourceChannelCode n 𝒱 𝒱' α β) :
    infoRD p d (c.distortion p W d) ≤ capacity W := by
  set μ := fbLaw (iidPMF p n) W (nfEnc (β := β) c.enc) n
  have hμ : IsPMF μ := fbLaw_isPMF (iidPMF_isPMF hp n) hW n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := mul_infoRD_le_mutualInfo (d := d) hp hμ hn (dist_fst_fbLaw hW n) (c.dec ∘ Prod.snd)
  have hD : ∑ ω, μ ω * seqDistortion d ω.1 ((c.dec ∘ Prod.snd) ω) = c.distortion p W d := by
    rw [Fintype.sum_prod_type, LossySourceChannelCode.distortion]
    exact sum_congr rfl fun v _ => sum_congr rfl fun y _ => by
      simp only [μ, fbLaw_nfEnc, Function.comp_apply]
  rw [hD] at h1
  have h2 := mutualInfo_comp_le hμ Prod.fst Prod.snd c.dec
  have h3 := mutualInfo_fbLaw_le (enc := nfEnc (β := β) c.enc) (iidPMF_isPMF hp n) hW n
  have : (n : ℝ) * infoRD p d (c.distortion p W d) ≤ n * capacity W := by linarith
  exact le_of_mul_le_mul_left this hn'

/-- **Theorem 10.4.1 (converse).** If the distortion `D` is achievable over a channel of capacity
`C`, then `R(D) ≤ C`. The book states the theorem as "achievable iff `C > R(D)`", whose strict
"only if" can fail at the boundary; the non-strict converse is the one its proof gives. -/
theorem IsAchievableSCDistortion.infoRD_le_capacity [Nonempty α] [Nonempty 𝒱'] (hp : IsPMF p)
    (hW : IsChannel W) {D : ℝ} (h : IsAchievableSCDistortion p W d D) :
    infoRD p d D ≤ capacity W := by
  obtain ⟨c, hc⟩ := h
  -- Every code has distortion at least `D_min`.
  have hmin : ∀ n, 0 < n → minDistortion p d ≤ (c n).distortion p W d := by
    intro n hn
    set μ := fbLaw (iidPMF p n) W (nfEnc (β := β) (c n).enc) n
    have hμ : IsPMF μ := fbLaw_isPMF (iidPMF_isPMF hp n) hW n
    have hlaw : ∀ i : Fin n, dist μ (fun ω => ω.1 i) = p := fun i => by
      rw [show (fun ω : (Fin n → 𝒱) × (Fin n → β) => ω.1 i) =
        (fun x : Fin n → 𝒱 => x i) ∘ Prod.fst from rfl, dist_comp_eq, dist_fst_fbLaw hW n,
        dist_iidPMF_apply hp]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hD : (c n).distortion p W d =
        (∑ i : Fin n, ∑ ω, μ ω * d (ω.1 i) ((c n).dec ω.2 i)) / n := by
      rw [LossySourceChannelCode.distortion, ← Fintype.sum_prod_type', sum_comm, sum_div]
      refine sum_congr rfl fun ω _ => ?_
      obtain ⟨v, y⟩ := ω
      simp only [μ, fbLaw_nfEnc, seqDistortion, mul_sum, sum_div]
      exact sum_congr rfl fun i _ => by ring
    rw [hD, le_div_iff₀ hn']
    calc minDistortion p d * n = ∑ _i : Fin n, minDistortion p d := by simp [mul_comm]
      _ ≤ _ := sum_le_sum fun i _ => by
          have h := sum_dist_mul μ (fun ω => ω.1 i) fun a => ⨅ y, d a y
          rw [hlaw i] at h
          calc minDistortion p d = ∑ ω, μ ω * ⨅ y, d (ω.1 i) y := h
            _ ≤ _ := sum_le_sum fun ω _ =>
                mul_le_mul_of_nonneg_left (ciInf_le_distortion d _ _) (hμ.nonneg ω)
  have hDmin : minDistortion p d ≤ D := le_of_forall_pos_le_add fun ε hε => by
    obtain ⟨n, hn⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
    exact (hmin n hn.2).trans hn.1
  refine infoRD_le_of_tendsto hp (Dₖ := fun k : ℕ => D + 1 / (k + 1)) (Rₖ := fun _ => capacity W)
    (fun k => by have : (0 : ℝ) < 1 / (k + 1) := by positivity
                 linarith) (fun k => ?_) ?_ tendsto_const_nhds
  · obtain ⟨n, hn⟩ := ((hc (1 / (k + 1)) (by positivity)).and (eventually_gt_atTop 0)).exists
    exact (infoRD_antitoneOn hp (hmin n hn.2) (show minDistortion p d ≤ D + 1 / (k + 1) by
      have : (0 : ℝ) < 1 / (k + 1) := by positivity
      linarith) hn.1).trans ((c n).infoRD_le_capacity hp hW hn.2)
  · simpa using (tendsto_const_nhds (x := D)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-! ### Achievability: separate source and channel coding -/

/-- The concatenation of a rate distortion code with `M` codewords and a channel code with
`M' ≥ M` messages: the index `fₙ(vⁿ)` is sent with the channel code, and a decoded index outside
`{0, …, M - 1}` is replaced by `0`. -/
def concatCode {n M M' : ℕ} (hM : 0 < M) (hMM : M ≤ M') (c₁ : RDCode M n 𝒱 𝒱')
    (c₂ : ChannelCode M' n α β) : LossySourceChannelCode n 𝒱 𝒱' α β where
  enc v := c₂.enc (Fin.castLE hMM (c₁.enc v))
  dec y := if h : (c₂.dec y : ℕ) < M then c₁.dec ⟨c₂.dec y, h⟩ else c₁.dec ⟨0, hM⟩

omit [Fintype α] [Fintype 𝒱'] in
/-- **Problem 10.17.** The distortion of the concatenated code is at most the distortion of the
rate distortion code plus `d_max` times the maximal probability of error of the channel code. -/
theorem distortion_concatCode_le [Finite 𝒱'] [Nonempty 𝒱] [Nonempty 𝒱'] (hp : IsPMF p)
    (hW : IsChannel W) (hd : ∀ x y, 0 ≤ d x y) {n M M' : ℕ} (hn : 0 < n) (hM : 0 < M)
    (hMM : M ≤ M') (c₁ : RDCode M n 𝒱 𝒱') (c₂ : ChannelCode M' n α β) :
    (concatCode hM hMM c₁ c₂).distortion p W d ≤
      c₁.distortion p d + maxDistortion d * c₂.maxErrProb W := by
  classical
  have hpn := iidPMF_isPMF hp n
  have hdmax := maxDistortion_nonneg hd
  rw [LossySourceChannelCode.distortion, RDCode.distortion]
  refine le_trans (sum_le_sum fun v _ => ?_) (le_of_eq (show ∑ v, (iidPMF p n v *
      seqDistortion d v (c₁.dec (c₁.enc v)) + iidPMF p n v * (maxDistortion d *
        c₂.maxErrProb W)) = _ by rw [sum_add_distrib, ← sum_mul, hpn.sum_eq_one, one_mul]))
  set w := Fin.castLE hMM (c₁.enc v)
  have hrow : ∀ y, iidPMF p n v * channelExt W n (c₂.enc w) y *
      seqDistortion d v ((concatCode hM hMM c₁ c₂).dec y) ≤
      iidPMF p n v * channelExt W n (c₂.enc w) y * seqDistortion d v (c₁.dec (c₁.enc v)) +
        iidPMF p n v * maxDistortion d *
          (if c₂.dec y ≠ w then channelExt W n (c₂.enc w) y else 0) := by
    intro y
    have hpc : 0 ≤ iidPMF p n v * channelExt W n (c₂.enc w) y :=
      mul_nonneg (hpn.nonneg v) (channelExt_nonneg hW _ y)
    by_cases hy : c₂.dec y = w
    · have : (concatCode hM hMM c₁ c₂).dec y = c₁.dec (c₁.enc v) := by
        have hlt : (c₂.dec y : ℕ) < M := by rw [hy]; exact (c₁.enc v).isLt
        simp only [concatCode, hlt, ↓reduceDIte]
        congr 1
        ext
        simp [hy, w]
      simp only [this, hy, ne_eq, not_true_eq_false, ↓reduceIte, mul_zero, add_zero, le_refl]
    · simp only [ne_eq, hy, not_false_eq_true, ↓reduceIte]
      have h1 := seqDistortion_le_maxDistortion d hn v ((concatCode hM hMM c₁ c₂).dec y)
      have h2 := seqDistortion_nonneg hd v (c₁.dec (c₁.enc v))
      nlinarith
  calc ∑ y, iidPMF p n v * channelExt W n (c₂.enc w) y *
        seqDistortion d v ((concatCode hM hMM c₁ c₂).dec y)
      ≤ ∑ y, (iidPMF p n v * channelExt W n (c₂.enc w) y * seqDistortion d v (c₁.dec (c₁.enc v)) +
        iidPMF p n v * maxDistortion d *
          (if c₂.dec y ≠ w then channelExt W n (c₂.enc w) y else 0)) := sum_le_sum fun y _ => hrow y
    _ = iidPMF p n v * seqDistortion d v (c₁.dec (c₁.enc v)) +
        iidPMF p n v * maxDistortion d * c₂.condErrProb W w := by
        rw [sum_add_distrib, ← mul_sum, ChannelCode.condErrProb]
        congr 1
        rw [← sum_mul, ← mul_sum, ((hW.ext n) (c₂.enc w)).sum_eq_one, mul_one]
    _ ≤ iidPMF p n v * seqDistortion d v (c₁.dec (c₁.enc v)) +
        iidPMF p n v * (maxDistortion d * c₂.maxErrProb W) := by
        rw [mul_assoc]
        gcongr
        · exact hpn.nonneg v
        · exact c₂.condErrProb_le_maxErrProb w

/-- **Theorem 10.4.1 (achievability).** If `R(D) < C`, the distortion `D` is achievable: a rate
distortion code of rate `R` with `R(D) < R < C` followed by a channel code of rate `R`. We also
assume `D ≥ D_min`, as `R(D)` is `0` below the smallest achievable distortion `D_min`. -/
theorem isAchievableSCDistortion_of_infoRD_lt [Nonempty α] [Nonempty 𝒱'] (hp : IsPMF p)
    (hW : IsChannel W) (hd : ∀ x y, 0 ≤ d x y) {D : ℝ} (hD : minDistortion p d ≤ D)
    (hC : infoRD p d D < capacity W) : IsAchievableSCDistortion p W d D := by
  have : Nonempty 𝒱 := by
    obtain ⟨a, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hp)
    exact ⟨a⟩
  obtain ⟨R, hR1, hR2⟩ := exists_between hC
  have hR0 : 0 < R := (infoRD_nonneg hp D).trans_lt hR1
  obtain ⟨c₁, hc₁⟩ := isAchievableRD_of_infoRD_lt hp hd hD hR1
  obtain ⟨c₂, hc₂⟩ := isAchievableRate_of_lt_capacity hW hR2
  have hM : ∀ n : ℕ, 0 < ⌊exp (n * R)⌋₊ := fun n =>
    Nat.floor_pos.2 (one_le_exp (by positivity))
  have hMM : ∀ n : ℕ, ⌊exp (n * R)⌋₊ ≤ ⌈exp (n * R)⌉₊ := fun n => Nat.floor_le_ceil _
  refine ⟨fun n => concatCode (hM n) (hMM n) (c₁ n) (c₂ n), fun ε hε => ?_⟩
  have hdmax := maxDistortion_nonneg hd
  have hT : Tendsto (fun n => maxDistortion d * (c₂ n).maxErrProb W) atTop (𝓝 0) := by
    simpa using hc₂.const_mul (maxDistortion d)
  filter_upwards [hc₁ (ε / 2) (by positivity), hT.eventually (gt_mem_nhds (half_pos hε)),
    eventually_gt_atTop 0] with n h1 h2 h3
  calc (concatCode (hM n) (hMM n) (c₁ n) (c₂ n)).distortion p W d
      ≤ (c₁ n).distortion p d + maxDistortion d * (c₂ n).maxErrProb W :=
        distortion_concatCode_le hp hW hd h3 (hM n) (hMM n) (c₁ n) (c₂ n)
    _ ≤ D + ε := by linarith

end InfoTheory
