/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyedChannel
public import InfoTheoryLib.Network.BCMoreCapable
public import InfoTheoryLib.Network.DMNetwork
public import InfoTheoryLib.MutualInformation.CsiszarSum
public import InfoTheoryLib.StateChannel.GPConverse

/-!
# The wiretap channel: definitions and the converse

Theorem 3 of Lecture 23 of El Gamal and Kim. A DM-WTC is a DM-BC `p(y, z | x)` with a legitimate
receiver `Y` and an eavesdropper `Z`. The sender keeps the message secret from the eavesdropper, in
the sense that the information leakage rate `(1/n) I(M; Zⁿ)` tends to `0`. The secrecy capacity is
`C_S = max_{p(u, x)} (I(U; Y) - I(U; Z))`, with `|𝒰| ≤ |𝒳|`.

This file proves the bound `|𝒰| ≤ |𝒳|` and the converse. The achievability is in
`InfoTheoryLib.Secrecy.WiretapAchievability`.

## Main definitions

* `WiretapCode M n α β`: a code, with a randomized encoder.
* `IsAchievableWiretap`, `wiretapCapacity`: the secrecy capacity, in bits.
* `wiretapGap q W`: `I(U; Y) - I(U; Z)`.
* `wiretapValue W`: the maximum of `wiretapGap` over `p(u, x)` with `|𝒰| = |𝒳|`, in nats.

## Main statements

* `condMutualInfo_eq_sum_condLawOf`: `I(A; B | C) = ∑_c p(c) I(A; B | C = c)`.
* `exists_support_le_of_linear`: a basic solution of a linear program.
* `exists_wiretapGap_reduce`: **the cardinality bound `|𝒰| ≤ |𝒳|`**.
* `condGap_le_wiretapValue`: the step of the converse that fixes `V = v`.
* `mutualInfo_sub_mutualInfo_eq_sum`: the Csiszár sum identity in the form of the converse.
* `WiretapCode.one_sub_errProb_mul_log_le`: `(1 - Pₑ) log M ≤ n C_S + I(M; Zⁿ) + log 2`.

## Implementation notes

The notes get the bound `|𝒰| ≤ |𝒳|` from the support lemma, with the Fenchel–Eggleston strengthening
of Carathéodory's theorem. We use that a maximum only has to be preserved, not the value of every
`p(u, x)`: for a fixed `p(x)`, the objective is linear in `p(u)`, and a basic solution of the linear
program has at most `|𝒳|` nonzero values.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Conditioning on one value -/

section Cond

variable {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c] {μ : Ω → ℝ}

open Classical in
/-- The law of `ω` given `C = c`. -/
def condLawOf (μ : Ω → ℝ) (C : Ω → c) (c₀ : c) : Ω → ℝ :=
  fun ω => if C ω = c₀ then μ ω / dist μ C c₀ else 0

omit [Fintype a] [Fintype c] in
/-- `p(f = x | C = c) = p(f = x, C = c) / p(C = c)`. -/
lemma dist_condLawOf (μ : Ω → ℝ) (C : Ω → c) (c₀ : c) (F : Ω → a) (x : a) :
    dist (condLawOf μ C c₀) F x = dist μ (pair F C) (x, c₀) / dist μ C c₀ := by
  classical
  simp only [dist, condLawOf, pair, Prod.mk.injEq, sum_div]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h₁ : F ω = x <;> by_cases h₂ : C ω = c₀ <;> simp [h₁, h₂]

omit [Fintype c] in
lemma condLawOf_isPMF [Finite c] (hμ : IsPMF μ) (C : Ω → c) {c₀ : c} (h : dist μ C c₀ ≠ 0) :
    IsPMF (condLawOf μ C c₀) := by
  have := Fintype.ofFinite c
  classical
  have h0 : 0 ≤ dist μ C c₀ := (hμ.dist C).nonneg c₀
  refine ⟨fun ω => ?_, ?_⟩
  · simp only [condLawOf]
    split_ifs
    exacts [div_nonneg (hμ.nonneg ω) h0, le_rfl]
  · simp only [condLawOf]
    have : ∑ ω, (if C ω = c₀ then μ ω / dist μ C c₀ else 0) =
        (∑ ω, if C ω = c₀ then μ ω else 0) / dist μ C c₀ := by
      rw [sum_div]
      exact sum_congr rfl fun ω _ => by split_ifs <;> simp
    rw [this]
    exact div_self h

omit [Fintype a] [Fintype c] in
lemma dist_pair_le_cond (hμ : IsPMF μ) (B : Ω → a) (C : Ω → c) (x : a) (z : c) :
    dist μ (pair B C) (x, z) ≤ dist μ C z := by
  classical
  simp only [dist, pair, Prod.mk.injEq]
  refine sum_le_sum fun ω _ => ?_
  by_cases h₁ : B ω = x <;> by_cases h₂ : C ω = z <;> simp [h₁, h₂, hμ.nonneg ω]

/-- `I(A; B | C) = ∑_c p(c) I(A; B | C = c)`. -/
theorem condMutualInfo_eq_sum_condLawOf (hμ : IsPMF μ) (A : Ω → a) (B : Ω → b) (C : Ω → c) :
    I[A : B | C ; μ] = ∑ c₀, dist μ C c₀ * I[A : B ; condLawOf μ C c₀] := by
  classical
  rw [condMutualInfo, condEntropy, condEntropy, Fintype.sum_prod_type_right, ← sum_sub_distrib]
  refine sum_congr rfl fun c₀ _ => ?_
  by_cases hc : dist μ C c₀ = 0
  · have h0 : ∀ b₀, dist μ (pair B C) (b₀, c₀) = 0 := fun b₀ => by
      have h₁ := (hμ.dist (pair B C)).nonneg (b₀, c₀)
      have h₂ := dist_pair_le_cond hμ B C b₀ c₀
      linarith
    simp [hc, h0]
  · have hP := condLawOf_isPMF hμ C hc
    rw [mutualInfo_eq_entropy_sub_condEntropy hP, mul_sub, condEntropy, mul_sum]
    congr 1
    · congr 1
      rw [entropyRV, condEntropyAt]
      congr 1
      funext a₀
      rw [dist_condLawOf, condDist]
      congr 1
      simp only [dist, pair, Prod.mk.injEq]
      refine sum_congr rfl fun ω _ => ?_
      by_cases h₁ : A ω = a₀ <;> by_cases h₂ : C ω = c₀ <;> simp [h₁, h₂]
    · refine sum_congr rfl fun b₀ _ => ?_
      have e₁ : dist (condLawOf μ C c₀) B b₀ = dist μ (pair B C) (b₀, c₀) / dist μ C c₀ :=
        dist_condLawOf μ C c₀ B b₀
      by_cases hb : dist μ (pair B C) (b₀, c₀) = 0
      · simp [e₁, hb]
      · have e₂ : condDist (condLawOf μ C c₀) A B b₀ = condDist μ A (pair B C) (b₀, c₀) := by
          funext a₀
          simp only [condDist]
          rw [dist_condLawOf, dist_condLawOf]
          have e₄ : dist μ (pair (pair B C) A) ((b₀, c₀), a₀) =
              dist μ (pair (pair B A) C) ((b₀, a₀), c₀) := by
            simp only [dist, pair, Prod.mk.injEq]
            refine sum_congr rfl fun ω _ => ?_
            by_cases h₁ : B ω = b₀ <;> by_cases h₂ : A ω = a₀ <;> by_cases h₃ : C ω = c₀ <;>
              simp [h₁, h₂, h₃]
          rw [e₄]
          field_simp
        simp only [condEntropyAt, e₁, e₂]
        field_simp

end Cond

/-! ### A basic solution of a linear program -/

section Basic

variable {υ E : Type*} [Fintype υ] [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- **A basic solution.** Let `r u` be vectors with `L (r u) = 1`. For weights `w ≥ 0` there are
weights `w' ≥ 0` with the same mean of the vectors, a mean of `f` that is no smaller, and at most
`dim E` nonzero values: move along a linear relation of the vectors, in the direction in which the
mean of `f` does not decrease, until a weight vanishes. -/
theorem exists_support_le_of_linear (L : E →ₗ[ℝ] ℝ) (r : υ → E) (hr : ∀ u, L (r u) = 1)
    (f : υ → ℝ) (w : υ → ℝ) (hw : ∀ u, 0 ≤ w u) :
    ∃ w' : υ → ℝ, (∀ u, 0 ≤ w' u) ∧ ∑ u, w' u • r u = ∑ u, w u • r u ∧
      ∑ u, w u * f u ≤ ∑ u, w' u * f u ∧
        (univ.filter fun u => w' u ≠ 0).card ≤ Module.finrank ℝ E := by
  induction hS : (univ.filter fun u => w u ≠ 0).card using Nat.strong_induction_on generalizing w
    with
  | _ k ih =>
    by_cases hk : k ≤ Module.finrank ℝ E
    · exact ⟨w, hw, rfl, le_rfl, hS ▸ hk⟩
    set S := univ.filter fun u => w u ≠ 0 with hSdef
    -- A linear relation among the vectors of the support.
    have hnl : ¬ LinearIndependent ℝ fun u : S => r u := fun hl => by
      have := hl.fintype_card_le_finrank
      rw [Fintype.card_coe, hS] at this
      exact hk this
    obtain ⟨g, hg0, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hnl
    set c₀ : υ → ℝ := fun u => if h : u ∈ S then g ⟨u, h⟩ else 0 with hc₀
    have hc₀S : ∀ u, u ∉ S → c₀ u = 0 := fun u hu => by simp [hc₀, hu]
    have hsum₀ : ∑ u, c₀ u • r u = 0 := by
      rw [← sum_subset (subset_univ S) fun u _ hu => by rw [hc₀S u hu, zero_smul], ← sum_coe_sort]
      rw [← hg0]
      refine sum_congr rfl fun u _ => ?_
      simp [hc₀]
    -- The direction in which the mean of `f` does not decrease.
    obtain ⟨c, hcS, hsum, hne, hcf⟩ : ∃ c : υ → ℝ, (∀ u, u ∉ S → c u = 0) ∧ ∑ u, c u • r u = 0 ∧
        (∃ u, c u ≠ 0) ∧ 0 ≤ ∑ u, c u * f u := by
      have hne₀ : ∃ u, c₀ u ≠ 0 := ⟨i₀, by simpa [hc₀] using hi₀⟩
      by_cases h : 0 ≤ ∑ u, c₀ u * f u
      · exact ⟨c₀, hc₀S, hsum₀, hne₀, h⟩
      · refine ⟨fun u => -c₀ u, fun u hu => by simp [hc₀S u hu], ?_, ?_, ?_⟩
        · simp only [neg_smul, sum_neg_distrib, hsum₀, neg_zero]
        · obtain ⟨u, hu⟩ := hne₀
          exact ⟨u, neg_ne_zero.2 hu⟩
        · simp only [neg_mul, sum_neg_distrib]
          linarith
    -- The relation has a negative value, as the values sum to `0`.
    have hzero : ∑ u, c u = 0 := by
      have := congrArg L hsum
      simpa [map_sum, map_smul, hr] using this
    have hneg : ∃ u, c u < 0 := by
      by_contra hpos
      push Not at hpos
      obtain ⟨u, hu⟩ := hne
      have := (sum_eq_zero_iff_of_nonneg fun u _ => hpos u).1 hzero u (mem_univ u)
      exact hu this
    set T := univ.filter fun u => c u < 0 with hT
    have hTne : T.Nonempty := by
      obtain ⟨u, hu⟩ := hneg
      exact ⟨u, mem_filter.2 ⟨mem_univ u, hu⟩⟩
    obtain ⟨u₀, hu₀, hmin⟩ := T.exists_min_image (fun u => w u / -c u) hTne
    set t := w u₀ / -c u₀ with ht
    have hcu₀ : c u₀ < 0 := (mem_filter.1 hu₀).2
    have ht0 : 0 ≤ t := div_nonneg (hw u₀) (by linarith)
    set w₁ : υ → ℝ := fun u => w u + t * c u with hw₁
    have hw₁0 : ∀ u, 0 ≤ w₁ u := fun u => by
      simp only [hw₁]
      by_cases hu : c u < 0
      · have h₁ := hmin u (mem_filter.2 ⟨mem_univ u, hu⟩)
        have h₂ : t * -c u ≤ w u := (le_div_iff₀ (by linarith)).1 h₁
        linarith
      · have := mul_nonneg ht0 (not_lt.1 hu)
        linarith [hw u]
    have hw₁u₀ : w₁ u₀ = 0 := by
      have hne0 : c u₀ ≠ 0 := hcu₀.ne
      have : w u₀ / -c u₀ * c u₀ = -w u₀ := by
        rw [div_neg, neg_mul, div_mul_cancel₀ _ hne0]
      simp only [hw₁, ht, this]
      ring
    -- The support shrinks.
    have hsub : (univ.filter fun u => w₁ u ≠ 0) ⊂ S := by
      refine (ssubset_iff_of_subset fun u hu => ?_).2 ⟨u₀, ?_, ?_⟩
      · refine mem_filter.2 ⟨mem_univ u, fun h0 => ?_⟩
        have hu' : u ∉ S := by simp [hSdef, h0]
        exact (mem_filter.1 hu).2 (by simp [hw₁, h0, hcS u hu'])
      · refine mem_filter.2 ⟨mem_univ _, fun h0 => ?_⟩
        have hu' : u₀ ∉ S := by simp [hSdef, h0]
        exact hcu₀.ne (hcS u₀ hu')
      · simp [hw₁u₀]
    obtain ⟨w', h₁, h₂, h₃, h₄⟩ := ih _ (hS ▸ card_lt_card hsub) w₁ hw₁0 rfl
    refine ⟨w', h₁, ?_, ?_, h₄⟩
    · rw [h₂]
      simp only [hw₁, add_smul, sum_add_distrib, mul_smul, ← smul_sum, hsum, smul_zero, add_zero]
    · refine le_trans ?_ h₃
      simp only [hw₁, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
      have := mul_nonneg ht0 hcf
      linarith

end Basic

/-! ### The value -/

section Value

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- **Theorem 3 of Lecture 23 of [elgamal2010], the objective.** `I(U; Y) - I(U; Z)`. -/
def wiretapGap {𝒰 : Type*} [Fintype 𝒰] (q : 𝒰 × α → ℝ) (W : α → β × γ → ℝ) : ℝ :=
  bcInfoUY₁ q W - bcInfoUY₂ q W

/-- **Theorem 3 of Lecture 23 of [elgamal2010], the value.** The maximum of `I(U; Y) - I(U; Z)` over
the laws `p(u, x)` with `|𝒰| = |𝒳|`, in nats. -/
def wiretapValue (W : α → β × γ → ℝ) : ℝ :=
  sSup ((fun q => wiretapGap q W) '' {q : Fin (Fintype.card α) × α → ℝ | IsPMF q})

variable {𝒰 : Type*} [Fintype 𝒰]

/-- The channel from `U` to the output of `T`, through `X` with `p(x | u) = r u x`. -/
def throughKernel (r : 𝒰 → α → ℝ) (T : α → β → ℝ) : 𝒰 → β → ℝ := fun u => outDist (r u) T

omit [Fintype 𝒰] in
lemma IsChannel.throughKernel {r : 𝒰 → α → ℝ} {T : α → β → ℝ} (hr : IsChannel r)
    (hT : IsChannel T) : IsChannel (throughKernel r T) := fun u => by
  refine ⟨fun y => sum_nonneg fun x _ => mul_nonneg ((hr u).nonneg x) ((hT x).nonneg y), ?_⟩
  simp only [InfoTheory.throughKernel, outDist]
  rw [sum_comm]
  simp only [← mul_sum, (hT _).sum_eq_one, mul_one, (hr u).sum_eq_one]

/-- `I(U; Y)` as the mutual information of the channel from `U` to `Y`. -/
lemma bcInfoUY₁_kernel (w : 𝒰 → ℝ) (r : 𝒰 → α → ℝ) (W : α → β × γ → ℝ) :
    bcInfoUY₁ (fun z : 𝒰 × α => w z.1 * r z.1 z.2) W =
      mutualInfoOf w (throughKernel r (bcMarg₁ W)) := by
  rw [bcInfoUY₁_eq, mutualInfoOf]
  congr 1
  funext z
  simp only [jointOf, throughKernel, outDist, mul_sum, mul_assoc]

/-- `I(U; Z)` as the mutual information of the channel from `U` to `Z`. -/
lemma bcInfoUY₂_kernel (w : 𝒰 → ℝ) (r : 𝒰 → α → ℝ) (W : α → β × γ → ℝ) :
    bcInfoUY₂ (fun z : 𝒰 × α => w z.1 * r z.1 z.2) W =
      mutualInfoOf w (throughKernel r (bcMarg₂ W)) := by
  rw [bcInfoUY₂_eq, mutualInfoOf]
  congr 1
  funext z
  simp only [jointOf, throughKernel, outDist, mul_sum, mul_assoc]

omit [Fintype β] in
/-- The output of the channel from `U`, as the output for the mean of the inputs. -/
lemma outDist_throughKernel (w : 𝒰 → ℝ) (r : 𝒰 → α → ℝ) (T : α → β → ℝ) :
    outDist w (throughKernel r T) = outDist (∑ u, w u • r u) T := by
  funext y
  simp only [outDist, throughKernel, mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun u _ => by ring

variable {W : α → β × γ → ℝ}

/-- The gap in terms of the mean input and the conditional outputs. -/
lemma wiretapGap_kernel {w : 𝒰 → ℝ} (hw : IsPMF w) {r : 𝒰 → α → ℝ} (hr : IsChannel r)
    (hW : IsChannel W) :
    wiretapGap (fun z : 𝒰 × α => w z.1 * r z.1 z.2) W =
      entropy (outDist (∑ u, w u • r u) (bcMarg₁ W)) -
        entropy (outDist (∑ u, w u • r u) (bcMarg₂ W)) +
          ∑ u, w u * (entropy (outDist (r u) (bcMarg₂ W)) - entropy (outDist (r u) (bcMarg₁ W))) :=
            by
  rw [wiretapGap, bcInfoUY₁_kernel, bcInfoUY₂_kernel,
    mutualInfoOf_eq hw (hr.throughKernel hW.bcMarg₁), mutualInfoOf_eq hw
      (hr.throughKernel hW.bcMarg₂),
    outDist_throughKernel, outDist_throughKernel]
  simp only [mul_sub, sum_sub_distrib, throughKernel]
  ring

/-- The wtPosterior `p(x | u)` of a law `p(u, x)`, with an arbitrary row where `p(u) = 0`. -/
def wtPosterior (q : 𝒰 × α → ℝ) (u : 𝒰) : α → ℝ := by
  classical
  exact if ∑ x, q (u, x) = 0 then uniformPMF α else fun x => q (u, x) / ∑ x', q (u, x')

lemma wtPosterior_isChannel {q : 𝒰 × α → ℝ} (hq : IsPMF q) : IsChannel (wtPosterior q) := fun u =>
  by
  classical
  have hα : Nonempty α := by
    obtain ⟨z⟩ : Nonempty (𝒰 × α) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
    exact ⟨z.2⟩
  simp only [wtPosterior]
  split_ifs with h
  · exact uniformPMF_isPMF
  · refine ⟨fun x => div_nonneg (hq.nonneg _) (sum_nonneg fun _ _ => hq.nonneg _), ?_⟩
    rw [← sum_div, div_self h]

/-- `p(u) p(x | u) = p(u, x)`. -/
lemma marg_mul_wtPosterior {q : 𝒰 × α → ℝ} (hq : IsPMF q) (z : 𝒰 × α) :
    (∑ x, q (z.1, x)) * wtPosterior q z.1 z.2 = q z := by
  classical
  simp only [wtPosterior]
  split_ifs with h
  · rw [h, zero_mul]
    exact ((sum_eq_zero_iff_of_nonneg fun _ _ => hq.nonneg _).1 h z.2 (mem_univ _)).symm
  · field_simp

lemma wiretapMarg_isPMF {q : 𝒰 × α → ℝ} (hq : IsPMF q) : IsPMF fun u => ∑ x, q (u, x) :=
  ⟨fun _ => sum_nonneg fun _ _ => hq.nonneg _, by
    rw [← hq.sum_eq_one, Fintype.sum_prod_type]⟩

/-- **The cardinality bound of Theorem 3 of Lecture 23 of [elgamal2010], page 23-20.** For every law
`p(u, x)` there is a law `p(u', x)` with `|𝒰'| = |𝒳|` and at least the same value of
`I(U; Y) - I(U; Z)`. -/
theorem exists_wiretapGap_reduce {q : 𝒰 × α → ℝ} (hq : IsPMF q) (hW : IsChannel W) :
    ∃ q' : Fin (Fintype.card α) × α → ℝ, IsPMF q' ∧ wiretapGap q W ≤ wiretapGap q' W := by
  classical
  set w : 𝒰 → ℝ := fun u => ∑ x, q (u, x) with hw
  set r := wtPosterior q with hrd
  have hwP : IsPMF w := wiretapMarg_isPMF hq
  have hr : IsChannel r := wtPosterior_isChannel hq
  have hqe : q = fun z : 𝒰 × α => w z.1 * r z.1 z.2 := funext fun z =>
    (marg_mul_wtPosterior hq z).symm
  set f : 𝒰 → ℝ := fun u => entropy (outDist (r u) (bcMarg₂ W)) -
    entropy (outDist (r u) (bcMarg₁ W))
    with hf
  set L : (α → ℝ) →ₗ[ℝ] ℝ := ∑ x, LinearMap.proj x with hL
  have hLr : ∀ u, L (r u) = 1 := fun u => by
    simp only [hL, LinearMap.sum_apply, LinearMap.proj_apply, (hr u).sum_eq_one]
  obtain ⟨w', hw'0, hmean, hobj, hcard⟩ :=
    exists_support_le_of_linear L r hLr f w hwP.nonneg
  rw [Module.finrank_fintype_fun_eq_card] at hcard
  -- The weights are a pmf.
  have hw'1 : ∑ u, w' u = 1 := by
    have := congrArg L hmean
    simpa [map_sum, map_smul, hLr, hwP.sum_eq_one] using this
  -- Relabel the support with `Fin |𝒳|`.
  set S := {u // w' u ≠ 0} with hS
  have hcardS : Fintype.card S ≤ Fintype.card (Fin (Fintype.card α)) := by
    rw [Fintype.card_fin, Fintype.card_subtype]
    exact hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcardS
  have hα : Nonempty α := by
    obtain ⟨z⟩ : Nonempty (𝒰 × α) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
    exact ⟨z.2⟩
  set w₂ : Fin (Fintype.card α) → ℝ := Function.extend e (fun s => w' s) 0 with hw₂
  set r₂ : Fin (Fintype.card α) → α → ℝ := Function.extend e (fun s => r s)
    (fun _ => uniformPMF α) with hr₂
  have hw₂e : ∀ s, w₂ (e s) = w' s := fun s => e.injective.extend_apply _ _ s
  have hr₂e : ∀ s, r₂ (e s) = r s := fun s => e.injective.extend_apply _ _ s
  have hw₂0 : ∀ j, j ∉ Set.range e → w₂ j = 0 := fun j hj => by
    simp only [hw₂]
    rw [Function.extend_apply' _ _ _ fun ⟨s, hs⟩ => hj ⟨s, hs⟩]
    rfl
  -- A sum over the new index is a sum over the old one.
  have hsum : ∀ G : (α → ℝ) → ℝ, ∑ j, w₂ j * G (r₂ j) = ∑ u, w' u * G (r u) := by
    intro G
    have h₁ : ∑ j, w₂ j * G (r₂ j) = ∑ s : S, w' s * G (r s) :=
      (Fintype.sum_of_injective e e.injective (fun s : S => w' s * G (r s))
        (fun j => w₂ j * G (r₂ j)) (fun j hj => by rw [hw₂0 j hj, zero_mul])
        fun s => by rw [hw₂e, hr₂e]).symm
    rw [h₁, ← sum_subset (subset_univ (univ.filter fun u => w' u ≠ 0))
      fun u _ hu => by
        have : w' u = 0 := by simpa using hu
        rw [this, zero_mul]]
    exact (sum_subtype (univ.filter fun u => w' u ≠ 0) (fun u => by simp)
      fun u => w' u * G (r u)).symm
  have hw₂P : IsPMF w₂ := by
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j ∈ Set.range e
      · obtain ⟨s, rfl⟩ := hj
        rw [hw₂e]
        exact hw'0 s
      · rw [hw₂0 j hj]
    · have := hsum fun _ => 1
      simpa [hw'1] using this
  have hr₂P : IsChannel r₂ := fun j => by
    by_cases hj : j ∈ Set.range e
    · obtain ⟨s, rfl⟩ := hj
      rw [hr₂e]
      exact hr s
    · simp only [hr₂]
      rw [Function.extend_apply' _ _ _ fun ⟨s, hs⟩ => hj ⟨s, hs⟩]
      exact uniformPMF_isPMF
  refine ⟨fun z => w₂ z.1 * r₂ z.1 z.2, ?_, ?_⟩
  · refine ⟨fun z => mul_nonneg (hw₂P.nonneg _) ((hr₂P _).nonneg _), ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, (hr₂P _).sum_eq_one, mul_one, hw₂P.sum_eq_one]
  · have hm₂ : ∑ j, w₂ j • r₂ j = ∑ u, w u • r u := by
      rw [← hmean]
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hsum fun v => v x
    rw [hqe, wiretapGap_kernel hwP hr hW, wiretapGap_kernel hw₂P hr₂P hW, hm₂]
    have h₂ := hsum fun v => entropy (outDist v (bcMarg₂ W)) - entropy (outDist v (bcMarg₁ W))
    rw [h₂]
    linarith

/-- The objective is continuous on the laws. -/
lemma continuousOn_wiretapGap {𝒰 : Type*} [Fintype 𝒰] (W : α → β × γ → ℝ) (hW : IsChannel W) :
    ContinuousOn (fun q : 𝒰 × α → ℝ => wiretapGap q W) {q | IsPMF q} := by
  have h : ∀ q : 𝒰 × α → ℝ, IsPMF q → wiretapGap q W =
      H[fun z : (𝒰 × α) × (β × γ) => z.1.1 ; jointOf q fun z => W z.2] +
        H[fun z : (𝒰 × α) × (β × γ) => z.2.1 ; jointOf q fun z => W z.2] -
        H[pair (fun z : (𝒰 × α) × (β × γ) => z.1.1) (fun z => z.2.1) ;
          jointOf q fun z => W z.2] -
      (H[fun z : (𝒰 × α) × (β × γ) => z.1.1 ; jointOf q fun z => W z.2] +
        H[fun z : (𝒰 × α) × (β × γ) => z.2.2 ; jointOf q fun z => W z.2] -
        H[pair (fun z : (𝒰 × α) × (β × γ) => z.1.1) (fun z => z.2.2) ;
          jointOf q fun z => W z.2]) := fun q hq => by
    rw [wiretapGap, bcInfoUY₁, bcInfoUY₂, mutualInfo_eq_add_sub (bcJoint_isPMF hq hW),
      mutualInfo_eq_add_sub (bcJoint_isPMF hq hW)]
    rfl
  refine ContinuousOn.congr (Continuous.continuousOn ?_) h
  have c₁ := continuous_entropyRV_jointOf_input (fun z : 𝒰 × α => W z.2)
    (fun z : (𝒰 × α) × (β × γ) => z.1.1)
  have c₂ := continuous_entropyRV_jointOf_input (fun z : 𝒰 × α => W z.2)
    (fun z : (𝒰 × α) × (β × γ) => z.2.1)
  have c₃ := continuous_entropyRV_jointOf_input (fun z : 𝒰 × α => W z.2)
    (pair (fun z : (𝒰 × α) × (β × γ) => z.1.1) (fun z => z.2.1))
  have c₄ := continuous_entropyRV_jointOf_input (fun z : 𝒰 × α => W z.2)
    (fun z : (𝒰 × α) × (β × γ) => z.2.2)
  have c₅ := continuous_entropyRV_jointOf_input (fun z : 𝒰 × α => W z.2)
    (pair (fun z : (𝒰 × α) × (β × γ) => z.1.1) (fun z => z.2.2))
  exact ((c₁.add c₂).sub c₃).sub ((c₁.add c₄).sub c₅)

/-- **Theorem 3 of Lecture 23 of [elgamal2010]: the maximum is attained.** -/
theorem exists_wiretapValue_eq [Nonempty α] (hW : IsChannel W) :
    ∃ q : Fin (Fintype.card α) × α → ℝ, IsPMF q ∧ wiretapGap q W = wiretapValue W := by
  have hcard : 0 < Fintype.card α := Fintype.card_pos
  have hne : Nonempty (Fin (Fintype.card α) × α) := ⟨(⟨0, hcard⟩, Classical.arbitrary α)⟩
  obtain ⟨q, hq, hmax⟩ := isCompact_setOf_isPMF.exists_isMaxOn
    ⟨uniformPMF _, uniformPMF_isPMF⟩ (continuousOn_wiretapGap (𝒰 := Fin (Fintype.card α)) W hW)
  refine ⟨q, hq, le_antisymm ?_ ?_⟩
  · exact le_csSup ⟨wiretapGap q W, by
      rintro _ ⟨q', hq', rfl⟩
      exact hmax hq'⟩ ⟨q, hq, rfl⟩
  · refine csSup_le ⟨_, q, hq, rfl⟩ ?_
    rintro _ ⟨q', hq', rfl⟩
    exact hmax hq'

/-- Every law `p(u, x)`, with any alphabet, has a gap at most the value. -/
theorem wiretapGap_le_value [Nonempty α] (hW : IsChannel W) {q : 𝒰 × α → ℝ} (hq : IsPMF q) :
    wiretapGap q W ≤ wiretapValue W := by
  obtain ⟨q', hq', h⟩ := exists_wiretapGap_reduce hq hW
  obtain ⟨q₀, hq₀, h₀⟩ := exists_wiretapValue_eq hW
  have hcard : 0 < Fintype.card α := Fintype.card_pos
  have hne : Nonempty (Fin (Fintype.card α) × α) := ⟨(⟨0, hcard⟩, Classical.arbitrary α)⟩
  obtain ⟨q₁, hq₁, hmax⟩ := isCompact_setOf_isPMF.exists_isMaxOn
    ⟨uniformPMF _, uniformPMF_isPMF⟩ (continuousOn_wiretapGap (𝒰 := Fin (Fintype.card α)) W hW)
  refine h.trans (le_csSup ⟨wiretapGap q₁ W, ?_⟩ ⟨q', hq', rfl⟩)
  rintro _ ⟨q'', hq'', rfl⟩
  exact hmax hq''

/-- With a constant `U`, the gap is `0`. So the value is nonnegative. -/
theorem wiretapValue_nonneg [Nonempty α] (hW : IsChannel W) : 0 ≤ wiretapValue W := by
  have hq : IsPMF fun z : Unit × α => uniformPMF α z.2 := by
    refine ⟨fun z => uniformPMF_isPMF.nonneg _, ?_⟩
    rw [Fintype.sum_prod_type]
    simp [uniformPMF_isPMF.sum_eq_one]
  refine le_trans (le_of_eq ?_) (wiretapGap_le_value hW hq)
  have h₁ : (fun z : Unit × α => uniformPMF α z.2) =
      fun z : Unit × α => (fun _ : Unit => (1 : ℝ)) z.1 * (fun _ => uniformPMF α) z.1 z.2 := by
    funext z
    simp
  have hw : IsPMF fun _ : Unit => (1 : ℝ) := ⟨fun _ => zero_le_one, by simp⟩
  have hr : IsChannel fun _ : Unit => uniformPMF α := fun _ => uniformPMF_isPMF
  rw [h₁, wiretapGap_kernel hw hr hW]
  simp

/-- **The step `(e)` of page 23-20 of [elgamal2010].** Suppose that, given `(U, X, V)`, the outputs
`T = (Y, Z)` come from `X` through the channel. Then `I(U; Y | V) - I(U; Z | V)` is at most the
value: it is the mean over `v` of a gap for the law of `(U, X)` given `V = v`. -/
theorem condGap_le_wiretapValue [Nonempty α] (hW : IsChannel W) {Ω ν : Type*} [Fintype Ω]
    [Fintype ν] {μ : Ω → ℝ} (hμ : IsPMF μ) (U : Ω → 𝒰) (V : Ω → ν) (X : Ω → α) (T : Ω → β × γ)
    (h : ∀ u x t v, dist μ (pair (pair (pair U X) T) V) (((u, x), t), v) =
      dist μ (pair (pair U X) V) ((u, x), v) * W x t) :
    I[U : (fun ω => (T ω).1) | V ; μ] - I[U : (fun ω => (T ω).2) | V ; μ] ≤ wiretapValue W := by
  classical
  rw [condMutualInfo_eq_sum_condLawOf hμ, condMutualInfo_eq_sum_condLawOf hμ, ← sum_sub_distrib]
  have hterm : ∀ v, dist μ V v * I[U : (fun ω => (T ω).1) ; condLawOf μ V v] -
      dist μ V v * I[U : (fun ω => (T ω).2) ; condLawOf μ V v] ≤ dist μ V v * wiretapValue W := by
    intro v
    rw [← mul_sub]
    by_cases hv : dist μ V v = 0
    · simp [hv]
    refine mul_le_mul_of_nonneg_left ?_ ((hμ.dist V).nonneg v)
    have hP := condLawOf_isPMF hμ V hv
    set μ' := condLawOf μ V v with hμ'
    set q := dist μ' (pair U X) with hq
    have hqP : IsPMF q := hP.dist _
    have hJ : bcJoint q W = dist μ' (pair (pair U X) T) := by
      funext ⟨⟨u, x⟩, t⟩
      rw [dist_condLawOf, h u x t v]
      simp only [bcJoint, jointOf, hq]
      rw [dist_condLawOf]
      ring
    have e₁ : bcInfoUY₁ q W = I[U : (fun ω => (T ω).1) ; μ'] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [hJ, ← dist_comp_eq]
      rfl
    have e₂ : bcInfoUY₂ q W = I[U : (fun ω => (T ω).2) ; μ'] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [hJ, ← dist_comp_eq]
      rfl
    have := wiretapGap_le_value hW hqP
    rwa [wiretapGap, e₁, e₂] at this
  refine (sum_le_sum fun v _ => hterm v).trans (le_of_eq ?_)
  rw [← sum_mul, (hμ.dist V).sum_eq_one, one_mul]

end Value

/-! ### The Csiszár sum identity -/

section Identity

variable {Ω 𝓜 β γ : Type*} [Fintype Ω] [Fintype 𝓜] [Fintype β] [Fintype γ] {μ : Ω → ℝ}

/-- `I(M; Z_iⁿ) = ∑_{j ≥ i} I(M; Z_j | Z_{j+1}ⁿ)`. -/
lemma mutualInfo_suffixRV_eq_sum (hμ : IsPMF μ) (M : Ω → 𝓜) (Z : ℕ → Ω → γ) (n : ℕ) :
    ∀ i ≤ n, I[M : suffixRV Z i n ; μ] = ∑ j ∈ Ico i n, I[M : Z j | suffixRV Z (j + 1) n ; μ] := by
  have key : ∀ d i, n - i = d → i ≤ n →
      I[M : suffixRV Z i n ; μ] = ∑ j ∈ Ico i n, I[M : Z j | suffixRV Z (j + 1) n ; μ] := by
    intro d
    induction d with
    | zero =>
      intro i h hi
      have hin : i = n := by omega
      subst hin
      simp only [Ico_self, sum_empty]
      have h₁ := mutualInfo_nonneg hμ M (suffixRV Z i i)
      have h₂ := mutualInfo_eq_entropy_sub_condEntropy' hμ M (suffixRV Z i i)
      have h₃ := condEntropy_nonneg hμ (suffixRV Z i i) M
      have h₄ := entropyRV_le_log_card hμ (suffixRV Z i i)
      have hcard : Fintype.card (Fin (i - i) → γ) = 1 := by simp
      rw [hcard] at h₄
      simp only [Nat.cast_one, log_one] at h₄
      linarith
    | succ d ih =>
      intro i h hi
      have hlt : i < n := by omega
      obtain ⟨f, hf, hfe⟩ := suffixRV_eq_cons Z hlt
      have h₁ : I[M : pair (Z i) (suffixRV Z (i + 1) n) ; μ] = I[M : suffixRV Z i n ; μ] :=
        mutualInfo_congr_right hμ M f hf hfe
      rw [← h₁, chain_rule_mutualInfo₂ hμ, ih (i + 1) (by omega) hlt,
        sum_eq_sum_Ico_succ_bot hlt]
      ring
  exact fun i hi => key _ i rfl hi

/-- **Pages 23-19 and 23-20 of [elgamal2010], (a) and (b).** With `Vᵢ = (Y^{i-1}, Z_{i+1}ⁿ)`, the
Csiszár sum identity gives
`I(M; Yⁿ) - I(M; Zⁿ) = ∑ᵢ (I(M; Yᵢ | Vᵢ) - I(M; Zᵢ | Vᵢ))`. -/
theorem mutualInfo_sub_mutualInfo_eq_sum (hμ : IsPMF μ) (M : Ω → 𝓜) (Y : ℕ → Ω → β) (Z : ℕ → Ω → γ)
    (n : ℕ) :
    I[M : prefixRV Y n ; μ] - I[M : suffixRV Z 0 n ; μ] =
      ∑ i ∈ range n, (I[M : Y i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ] -
        I[M : Z i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ]) := by
  have hcs₁ := csiszar_sum hμ Z Y M n
  have hcs₂ := csiszar_sum' hμ Z Y n
  have hY : ∀ i, I[M : Y i | prefixRV Y i ; μ] +
      I[suffixRV Z (i + 1) n : Y i | pair (prefixRV Y i) M ; μ] =
      I[suffixRV Z (i + 1) n : Y i | prefixRV Y i ; μ] +
        I[M : Y i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ] := fun i => by
    have h₁ := chain_rule_condMutualInfo hμ (Y i) (suffixRV Z (i + 1) n) M (prefixRV Y i)
    have h₂ := chain_rule_condMutualInfo hμ (Y i) M (suffixRV Z (i + 1) n) (prefixRV Y i)
    have h₃ : I[Y i : pair (suffixRV Z (i + 1) n) M | prefixRV Y i ; μ] =
        I[Y i : pair M (suffixRV Z (i + 1) n) | prefixRV Y i ; μ] := by
      rw [condMutualInfo, condMutualInfo]
      congr 1
      exact condEntropy_congr_right hμ _ (fun w => (w.1.swap, w.2))
        (fun a b hab => by
          simp only [Prod.mk.injEq] at hab
          exact Prod.ext (Prod.swap_injective hab.1) hab.2) fun _ => rfl
    have h₄ : I[Y i : M | pair (suffixRV Z (i + 1) n) (prefixRV Y i) ; μ] =
        I[Y i : M | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ] := by
      rw [condMutualInfo, condMutualInfo]
      congr 1
      · exact condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
      · exact condEntropy_congr_right hμ _ (fun w => (w.1, w.2.swap))
          (fun a b hab => by
            simp only [Prod.mk.injEq] at hab
            exact Prod.ext hab.1 (Prod.swap_injective hab.2)) fun _ => rfl
    have h₅ : I[Y i : suffixRV Z (i + 1) n | pair M (prefixRV Y i) ; μ] =
        I[Y i : suffixRV Z (i + 1) n | pair (prefixRV Y i) M ; μ] := by
      rw [condMutualInfo, condMutualInfo]
      congr 1
      · exact condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
      · exact condEntropy_congr_right hμ _ (fun w => (w.1, w.2.swap))
          (fun a b hab => by
            simp only [Prod.mk.injEq] at hab
            exact Prod.ext hab.1 (Prod.swap_injective hab.2)) fun _ => rfl
    rw [condMutualInfo_comm hμ M, condMutualInfo_comm hμ (suffixRV Z (i + 1) n),
      condMutualInfo_comm hμ (suffixRV Z (i + 1) n), condMutualInfo_comm hμ M]
    linarith
  have hZ : ∀ i, I[M : Z i | suffixRV Z (i + 1) n ; μ] +
      I[prefixRV Y i : Z i | pair (suffixRV Z (i + 1) n) M ; μ] =
      I[prefixRV Y i : Z i | suffixRV Z (i + 1) n ; μ] +
        I[M : Z i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; μ] := fun i => by
    have h₁ := chain_rule_condMutualInfo hμ (Z i) (prefixRV Y i) M (suffixRV Z (i + 1) n)
    have h₂ := chain_rule_condMutualInfo hμ (Z i) M (prefixRV Y i) (suffixRV Z (i + 1) n)
    have h₃ : I[Z i : pair (prefixRV Y i) M | suffixRV Z (i + 1) n ; μ] =
        I[Z i : pair M (prefixRV Y i) | suffixRV Z (i + 1) n ; μ] := by
      rw [condMutualInfo, condMutualInfo]
      congr 1
      exact condEntropy_congr_right hμ _ (fun w => (w.1.swap, w.2))
        (fun a b hab => by
          simp only [Prod.mk.injEq] at hab
          exact Prod.ext (Prod.swap_injective hab.1) hab.2) fun _ => rfl
    have h₅ : I[Z i : prefixRV Y i | pair M (suffixRV Z (i + 1) n) ; μ] =
        I[Z i : prefixRV Y i | pair (suffixRV Z (i + 1) n) M ; μ] := by
      rw [condMutualInfo, condMutualInfo]
      congr 1
      · exact condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
      · exact condEntropy_congr_right hμ _ (fun w => (w.1, w.2.swap))
          (fun a b hab => by
            simp only [Prod.mk.injEq] at hab
            exact Prod.ext hab.1 (Prod.swap_injective hab.2)) fun _ => rfl
    rw [condMutualInfo_comm hμ M, condMutualInfo_comm hμ (prefixRV Y i),
      condMutualInfo_comm hμ (prefixRV Y i), condMutualInfo_comm hμ M]
    linarith
  rw [mutualInfo_prefixRV_eq_sum hμ, mutualInfo_suffixRV_eq_sum hμ M Z n 0 (Nat.zero_le n),
    Nat.Ico_zero_eq_range, ← sum_sub_distrib, ]
  have key : ∑ i ∈ range n, (I[M : Y i | prefixRV Y i ; μ] - I[M : Z i | suffixRV Z (i + 1) n ;
    μ]) =
      ∑ i ∈ range n, ((I[M : Y i | prefixRV Y i ; μ] +
        I[suffixRV Z (i + 1) n : Y i | pair (prefixRV Y i) M ; μ] -
        I[suffixRV Z (i + 1) n : Y i | prefixRV Y i ; μ]) -
        (I[M : Z i | suffixRV Z (i + 1) n ; μ] +
          I[prefixRV Y i : Z i | pair (suffixRV Z (i + 1) n) M ; μ] -
          I[prefixRV Y i : Z i | suffixRV Z (i + 1) n ; μ])) := by
    simp only [sum_sub_distrib, sum_add_distrib]
    rw [hcs₁, hcs₂]
    ring
  rw [key]
  refine sum_congr rfl fun i _ => ?_
  have := hY i
  have := hZ i
  linarith

end Identity

/-! ### Codes and the converse -/

section Code

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- **Lecture 23 of [elgamal2010], page 23-8.** A code for the DM-WTC: a randomized encoder
`p(xⁿ | m)` and a decoder `m̂(yⁿ)`. The notes also allow an error message, which does not help. -/
structure WiretapCode (M n : ℕ) (α β : Type*) [Fintype α] where
  /-- The randomized encoder. -/
  enc : Fin M → (Fin n → α) → ℝ
  /-- Each row of the encoder is a pmf. -/
  isChannel_enc : IsChannel enc
  /-- The decoder. -/
  dec : (Fin n → β) → Fin M

namespace WiretapCode

variable {M n : ℕ} (W : α → β × γ → ℝ) (c : WiretapCode M n α β)

/-- The law of `(M, Xⁿ)`, for a uniform message. -/
def inputLaw : Fin M × (Fin n → α) → ℝ := jointOf (uniformPMF _) c.enc

/-- The law of `((M, Xⁿ), (Yⁿ, Zⁿ))`. -/
def law : (Fin M × (Fin n → α)) × (Fin n → β × γ) → ℝ :=
  jointOf c.inputLaw fun z => channelExt W n z.2

/-- The received sequence `Yⁿ`. -/
def outY : (Fin M × (Fin n → α)) × (Fin n → β × γ) → Fin n → β := fun z i => (z.2 i).1

/-- The sequence `Zⁿ` of the eavesdropper. -/
def outZ : (Fin M × (Fin n → α)) × (Fin n → β × γ) → Fin n → γ := fun z i => (z.2 i).2

/-- The probability of error `P{M ≠ M̂(Yⁿ)}`. -/
def errProb : ℝ := InfoTheory.errProb (c.law W) (fun z => z.1.1) outY c.dec

/-- The information leakage `I(M; Zⁿ)`, which is `n` times the leakage rate. -/
def leakage : ℝ := I[fun z => z.1.1 : outZ ; c.law W]

variable {W c}

omit [Fintype β] [Fintype γ] in
lemma inputLaw_isPMF [NeZero M] : IsPMF c.inputLaw := by
  have : Nonempty (Fin M) := ⟨0⟩
  exact jointOf_isPMF uniformPMF_isPMF c.isChannel_enc

lemma law_isPMF [NeZero M] (hW : IsChannel W) : IsPMF (c.law W) :=
  jointOf_isPMF inputLaw_isPMF fun z => hW.ext n z.2

lemma entropy_message [NeZero M] (hW : IsChannel W) : H[fun z => z.1.1 ; c.law W] = log M := by
  have : Nonempty (Fin M) := ⟨0⟩
  have e : dist (c.law W) (fun z => z.1.1) = uniformPMF (Fin M) := by
    have h := dist_comp_eq (c.law W) Prod.fst (Prod.fst : Fin M × (Fin n → α) → _)
    have e' : dist (c.law W) Prod.fst = c.inputLaw := dist_jointOf_fst fun z => hW.ext n z.2
    rw [e', inputLaw, dist_jointOf_fst c.isChannel_enc] at h
    exact h
  rw [entropyRV, e, entropy_uniformPMF, Fintype.card_fin]

end WiretapCode

/-- **Disjoint letters of a memoryless channel.** If `F` does not depend on the output at time `i`,
then `E F(tⁿ) g(tᵢ) = E F(tⁿ) · ∑ₐ W(a | xᵢ) g(a)`, given the input `xⁿ`. -/
lemma sum_channelExt_mul_coord {α' τ : Type*} [Fintype τ] {W : α' → τ → ℝ} (hW : IsChannel W)
    {n : ℕ} (x : Fin n → α') (i : Fin n) {F : (Fin n → τ) → ℝ}
    (hF : ∀ t a, F (Function.update t i a) = F t) (g : τ → ℝ) :
    ∑ t, channelExt W n x t * (F t * g (t i)) =
      (∑ t, channelExt W n x t * F t) * ∑ a, W (x i) a * g a := by
  classical
  set Φ : (Fin n → τ) × τ → (Fin n → τ) × τ := fun z => (Function.update z.1 i z.2, z.1 i)
  have hΦ : Function.Involutive Φ := fun z => by
    simp [Φ]
  have hext : ∀ t a, channelExt W n x (Function.update t i a) * W (x i) (t i) =
      channelExt W n x t * W (x i) a := by
    intro t a
    simp only [channelExt]
    rw [← mul_prod_erase univ _ (mem_univ i),
      ← mul_prod_erase univ (fun j => W (x j) (t j)) (mem_univ i)]
    have e : ∏ j ∈ univ.erase i, W (x j) (Function.update t i a j) =
        ∏ j ∈ univ.erase i, W (x j) (t j) :=
      prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.1 hj).1]
    rw [e, Function.update_self]
    ring
  have h := Equiv.sum_comp (hΦ.toPerm)
    (fun z : (Fin n → τ) × τ => channelExt W n x z.1 * (F z.1 * g (z.1 i)) * W (x i) z.2)
  have hL : ∑ z : (Fin n → τ) × τ, channelExt W n x z.1 * (F z.1 * g (z.1 i)) * W (x i) z.2 =
      ∑ t, channelExt W n x t * (F t * g (t i)) := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_sum, (hW (x i)).sum_eq_one, mul_one]
  have hR : ∑ z : (Fin n → τ) × τ, channelExt W n x (Φ z).1 * (F (Φ z).1 * g ((Φ z).1 i)) *
      W (x i) (Φ z).2 = (∑ t, channelExt W n x t * F t) * ∑ a, W (x i) a * g a := by
    rw [Fintype.sum_prod_type, sum_mul]
    refine sum_congr rfl fun t _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [Φ, hF, Function.update_self]
    have := hext t a
    linear_combination (F t * g a) * this
  rw [← hL, ← hR]
  exact h.symm

namespace WiretapCode

variable {M n : ℕ} {W : α → β × γ → ℝ} (c : WiretapCode M n α β)

/-- **The memoryless property in the converse.** Given `(M, Xᵢ)` and a function `V` of the outputs
at the other times, the output at time `i` comes from `Xᵢ` through the channel. -/
lemma dist_coord_eq (hW : IsChannel W) {ν 𝒰 : Type*} [Finite ν] [Finite 𝒰] (i : Fin n)
    (U : Fin M × (Fin n → α) → 𝒰) (V : (Fin n → β × γ) → ν)
    (hV : ∀ t a, V (Function.update t i a) = V t) (u : 𝒰) (x : α) (t : β × γ) (v : ν) :
    dist (c.law W) (pair (pair (pair (fun z => U z.1) fun z => z.1.2 i) fun z => z.2 i)
        fun z => V z.2) (((u, x), t), v) =
      dist (c.law W) (pair (pair (fun z => U z.1) fun z => z.1.2 i) fun z => V z.2) ((u, x), v) *
        W x t := by
  have := Fintype.ofFinite ν
  have := Fintype.ofFinite 𝒰
  classical
  simp only [dist, pair, Prod.mk.injEq, law, jointOf]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type (f := fun w : (Fin M × (Fin n → α)) ×
    (Fin n → β × γ) => _), sum_mul]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : U a = u ∧ a.2 i = x
  · have hF := sum_channelExt_mul_coord hW a.2 i (F := fun t' => if V t' = v then (1 : ℝ) else 0)
      (fun t' b => by simp [hV]) (fun b => if b = t then (1 : ℝ) else 0)
    have hg : ∑ b, W (a.2 i) b * (if b = t then (1 : ℝ) else 0) = W x t := by
      rw [ha.2]
      simp
    rw [hg] at hF
    have e₁ : ∀ t' : Fin n → β × γ, (if ((U a = u ∧ a.2 i = x) ∧ t' i = t) ∧ V t' = v then
        c.inputLaw a * channelExt W n a.2 t' else 0) = c.inputLaw a *
          (channelExt W n a.2 t' * ((if V t' = v then 1 else 0) * if t' i = t then 1 else 0)) :=
      fun t' => by
        by_cases h₁ : t' i = t <;> by_cases h₂ : V t' = v <;> simp [ha, h₁, h₂]
    have e₂ : ∀ t' : Fin n → β × γ, (if (U a = u ∧ a.2 i = x) ∧ V t' = v then
        c.inputLaw a * channelExt W n a.2 t' else 0) = c.inputLaw a *
          (channelExt W n a.2 t' * if V t' = v then 1 else 0) := fun t' => by
      by_cases h₂ : V t' = v <;> simp [ha, h₂]
    simp only [e₁, e₂, ← mul_sum, hF]
    ring
  · have e₁ : ∀ t' : Fin n → β × γ, ¬(((U a = u ∧ a.2 i = x) ∧ t' i = t) ∧ V t' = v) :=
      fun t' h => ha h.1.1
    have e₂ : ∀ t' : Fin n → β × γ, ¬((U a = u ∧ a.2 i = x) ∧ V t' = v) := fun t' h => ha h.1
    simp [e₁, e₂]

/-- **Pages 23-19 and 23-20 of [elgamal2010]: the converse for one code.**
`(1 - Pₑ) log M ≤ n C_S + I(M; Zⁿ) + log 2`. -/
theorem one_sub_errProb_mul_log_le [NeZero M] [Nonempty α] (hW : IsChannel W) :
    (1 - c.errProb W) * log M ≤ n * wiretapValue W + c.leakage W + log 2 := by
  classical
  have hμ := law_isPMF (c := c) hW
  obtain ⟨t₀⟩ : Nonempty (β × γ) := by
    have := card_pos_of_isPMF (hW (Classical.arbitrary α))
    exact Fintype.card_pos_iff.1 this
  set Y : ℕ → (Fin M × (Fin n → α)) × (Fin n → β × γ) → β :=
    fun j z => if h : j < n then (z.2 ⟨j, h⟩).1 else t₀.1 with hY
  set Z : ℕ → (Fin M × (Fin n → α)) × (Fin n → β × γ) → γ :=
    fun j z => if h : j < n then (z.2 ⟨j, h⟩).2 else t₀.2 with hZ
  set Mv : (Fin M × (Fin n → α)) × (Fin n → β × γ) → Fin M := fun z => z.1.1 with hMv
  have hYn : prefixRV Y n = outY := by
    funext z j
    simp [prefixRV, hY, outY, j.2]
  have hZn : I[Mv : suffixRV Z 0 n ; c.law W] = I[Mv : outZ ; c.law W] := by
    refine mutualInfo_congr_right hμ Mv (fun v j => v ⟨j, by have := j.2; omega⟩)
      (fun a b hab => ?_) fun z => ?_
    · funext j
      have := congrFun hab ⟨j, by have := j.2; omega⟩
      simpa using this
    · funext j
      have hj : (0 + (j : ℕ)) < n := by have := j.2; omega
      simp [suffixRV, hZ, outZ]
  -- Fano's inequality.
  have hF := fano_weak hμ Mv outY c.dec
  rw [Fintype.card_fin] at hF
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ Mv outY
  have hM := entropy_message (c := c) hW
  -- The single-letterization.
  have hsum : I[Mv : prefixRV Y n ; c.law W] - I[Mv : suffixRV Z 0 n ; c.law W] ≤
      n * wiretapValue W := by
    rw [mutualInfo_sub_mutualInfo_eq_sum hμ]
    have hterm : ∀ i ∈ range n,
        I[Mv : Y i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; c.law W] -
        I[Mv : Z i | pair (prefixRV Y i) (suffixRV Z (i + 1) n) ; c.law W] ≤
          wiretapValue W := by
      intro i hi
      have hin : i < n := mem_range.1 hi
      set V' : (Fin n → β × γ) → (Fin i → β) × (Fin (n - (i + 1)) → γ) :=
        fun t => (fun j => if h : (j : ℕ) < n then (t ⟨j, h⟩).1 else t₀.1,
          fun j => if h : i + 1 + (j : ℕ) < n then (t ⟨i + 1 + j, h⟩).2 else t₀.2) with hV'
      have hVz : pair (prefixRV Y i) (suffixRV Z (i + 1) n) = fun z => V' z.2 := by
        funext z
        refine Prod.ext ?_ ?_
        · funext j
          simp only [pair, prefixRV, hY, hV']
        · funext j
          simp only [pair, suffixRV, hZ, hV']
      have hV : ∀ t a, V' (Function.update t ⟨i, hin⟩ a) = V' t := fun t a => by
        refine Prod.ext ?_ ?_
        · funext j
          have hj : (j : ℕ) < i := j.2
          simp only [hV']
          split_ifs with h
          · rw [Function.update_of_ne]
            intro he
            have := congrArg Fin.val he
            simp only at this
            omega
          · rfl
        · funext j
          simp only [hV']
          split_ifs with h
          · rw [Function.update_of_ne]
            intro he
            have := congrArg Fin.val he
            simp only at this
            omega
          · rfl
      rw [hVz]
      have h := condGap_le_wiretapValue hW hμ Mv (fun z => V' z.2)
        (fun z => z.1.2 ⟨i, hin⟩) (fun z => z.2 ⟨i, hin⟩) fun u x t v =>
          c.dist_coord_eq hW ⟨i, hin⟩ Prod.fst V' hV u x t v
      have e₁ : Y i = fun z => (z.2 ⟨i, hin⟩).1 := by
        funext z
        simp [hY, hin]
      have e₂ : Z i = fun z => (z.2 ⟨i, hin⟩).2 := by
        funext z
        simp [hZ, hin]
      rw [e₁, e₂]
      exact h
    refine (sum_le_sum hterm).trans (le_of_eq ?_)
    simp
  rw [hYn, hZn] at hsum
  have h₁ : c.errProb W = InfoTheory.errProb (c.law W) Mv outY c.dec := rfl
  have h₂ : c.leakage W = I[Mv : outZ ; c.law W] := rfl
  rw [← h₁] at hF
  rw [h₂]
  nlinarith

end WiretapCode

/-- **Page 23-9 of [elgamal2010].** A secrecy rate `R`, in bits, is achievable if for every `ε` and
all large `n` there is a code with `2 ^ ⌈nR⌉` messages, with probability of error at most `ε` and
leakage rate at most `ε`. -/
def IsAchievableWiretap (W : α → β × γ → ℝ) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ c : WiretapCode (2 ^ ⌈n * R⌉₊) n α β,
    c.errProb W ≤ ε ∧ c.leakage W ≤ n * ε

/-- **Page 23-9 of [elgamal2010].** The secrecy capacity `C_S`, in bits. -/
def wiretapCapacity (W : α → β × γ → ℝ) : ℝ := sSup {R | IsAchievableWiretap W R}

/-- **Pages 23-19 and 23-20 of [elgamal2010]: the converse of Theorem 3.** An achievable rate is at
most the value. -/
theorem IsAchievableWiretap.le [Nonempty α] {W : α → β × γ → ℝ} (hW : IsChannel W) {R : ℝ}
    (h : IsAchievableWiretap W R) : R * log 2 ≤ wiretapValue W := by
  have hl := log_pos one_lt_two
  refine le_of_forall_eventually_mul_le (mul_nonneg h.1 hl.le) fun ε hε => ?_
  refine ⟨log 2, ?_⟩
  filter_upwards [h.2 (min ε (1 / 2)) (by positivity)] with n hn
  obtain ⟨c, hc₁, hc₂⟩ := hn
  have : NeZero (2 ^ ⌈n * R⌉₊) := ⟨by positivity⟩
  have h₁ := c.one_sub_errProb_mul_log_le hW
  have h₂ := le_log_two_pow_ceil n R
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hP : 0 ≤ 1 - c.errProb W := by
    have := hc₁.trans (min_le_right _ _)
    linarith
  have hmin : c.errProb W ≤ ε := hc₁.trans (min_le_left _ _)
  have hleak : c.leakage W ≤ n * ε :=
    hc₂.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hn0)
  have hb : (1 - ε) * (n * (R * log 2)) ≤ (1 - c.errProb W) * log (2 ^ ⌈n * R⌉₊ : ℕ) := by
    have ha : 0 ≤ n * (R * log 2) := mul_nonneg hn0 (mul_nonneg h.1 hl.le)
    calc (1 - ε) * (n * (R * log 2)) ≤ (1 - c.errProb W) * (n * (R * log 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) ha
      _ ≤ _ := mul_le_mul_of_nonneg_left h₂ hP
  nlinarith

end Code

end InfoTheory
