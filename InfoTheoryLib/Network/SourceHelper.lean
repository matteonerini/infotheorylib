/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.SlepianWolfBits
public import InfoTheoryLib.StateChannel.Multicoding

/-!
# Lossless source coding with a helper: achievability

The source `Xⁿ` is to be recovered losslessly from the index `M₁` of its encoder and the index `M₂`
of a helper that observes the correlated `Yⁿ`. Theorem 2 of Lecture 11 says that the optimal rate
region is `R₁ ≥ H(X | U)`, `R₂ ≥ I(Y; U)` for some `p(u | y)`. This file proves that these rates are
achievable, and `Network.SourceHelperConverse` the converse.

The helper describes `Yⁿ` by a jointly typical sequence of a random codebook `Uⁿ(m₂)`, which is
possible by the covering lemma if `R₂ > I(Y; U)`. As `U → Y → X`, the sequence `Uⁿ` is then jointly
typical with `Xⁿ` by the conditional typicality lemma. The encoder of `Xⁿ` uses random binning, and
the decoder finds the unique sequence of the bin that is jointly typical with `Uⁿ`.

## Main definitions

* `HelperCode M₁ M₂ n α β`: the codes, with `HelperCode.errProb`.
* `helperLaw q κ`: the law `p(x, y) p(u | y)`.
* `helperCond q κ`, `helperInfo q κ`: `H(X | U)` and `I(Y; U)`, in nats.
* `IsAchievableHelperBits q R₁ R₂`, `helperOptimalRegionBits q`, `helperRegionBits q`.

## Main statements

* `exists_bins_code`: random binning, for any sets of allowed sequences.
* `exists_helper_code_le`: the bound on the probability of error.
* `isAchievableHelperBits_of_lt`: **the achievability of Theorem 2 of Lecture 11**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 11
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

variable {α β 𝒰 : Type*} [Fintype α] [Fintype β] [Fintype 𝒰]

/-- **Lecture 11 of [elgamal2010], page 11-21.** A code for lossless source coding with a helper: an
encoder for the source, an encoder for the helper and a decoder of the source. -/
structure HelperCode (M₁ M₂ n : ℕ) (α β : Type*) where
  /-- The encoder of the source. -/
  enc₁ : (Fin n → α) → Fin M₁
  /-- The encoder of the helper. -/
  enc₂ : (Fin n → β) → Fin M₂
  /-- The decoder. -/
  dec : Fin M₁ × Fin M₂ → Fin n → α

open Classical in
/-- **Lecture 11 of [elgamal2010], page 11-21.** The probability of error `P{X̂ⁿ ≠ Xⁿ}`. -/
def HelperCode.errProb {M₁ M₂ n : ℕ} (c : HelperCode M₁ M₂ n α β) (q : α × β → ℝ) : ℝ :=
  ∑ z, if c.dec (c.enc₁ z.1, c.enc₂ z.2) ≠ z.1 then jointIid q n z else 0

lemma HelperCode.errProb_nonneg {M₁ M₂ n : ℕ} (c : HelperCode M₁ M₂ n α β) {q : α × β → ℝ}
    (hq : IsPMF q) : 0 ≤ c.errProb q := by
  classical
  exact sum_nonneg fun z _ => by split_ifs <;> simp [jointIid_nonneg hq.nonneg]

/-- **Lecture 11 of [elgamal2010], page 11-23.** The law `p(x, y) p(u | y)` of `((X, Y), U)`. -/
def helperLaw (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) : (α × β) × 𝒰 → ℝ := jointOf q fun z => κ z.2

lemma helperLaw_isPMF {q : α × β → ℝ} (hq : IsPMF q) {κ : β → 𝒰 → ℝ} (hκ : ∀ y, IsPMF (κ y)) :
    IsPMF (helperLaw q κ) :=
  jointOf_isPMF hq fun z => hκ z.2

/-- `H(X | U)` under the law `p(x, y) p(u | y)`, in nats. -/
def helperCond (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) : ℝ :=
  H[fun z : (α × β) × 𝒰 => z.1.1 | Prod.snd ; helperLaw q κ]

/-- `I(Y; U)` under the law `p(x, y) p(u | y)`, in nats. -/
def helperInfo (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) : ℝ :=
  I[fun z : (α × β) × 𝒰 => z.1.2 : Prod.snd ; helperLaw q κ]

/-- **Lecture 11 of [elgamal2010], page 11-21.** A rate pair, in bits, is achievable if there are
codes with the index sets `[1 : 2^{nRⱼ})` whose probability of error tends to `0`. -/
def IsAchievableHelperBits (q : α × β → ℝ) (R₁ R₂ : ℝ) : Prop :=
  0 ≤ R₁ ∧ 0 ≤ R₂ ∧ ∃ c : ∀ n : ℕ, HelperCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β,
    Tendsto (fun n => (c n).errProb q) atTop (𝓝 0)

/-- **Lecture 11 of [elgamal2010], page 11-21.** The optimal rate region. -/
def helperOptimalRegionBits (q : α × β → ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableHelperBits q R.1 R.2}

/-- **Theorem 2 of Lecture 11 of [elgamal2010], the region.** `R₁ ≥ H(X | U)`, `R₂ ≥ I(Y; U)` for
some `p(u | y)`, in bits, with `U` on `Fin k`. -/
def helperRegionBits (q : α × β → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (k : ℕ) (κ : β → Fin k → ℝ), (∀ y, IsPMF (κ y)) ∧ helperCond q κ / log 2 ≤ R.1 ∧
    helperInfo q κ / log 2 ≤ R.2}

/-! ### Random binning -/

section Binning

variable {n M₁ M₂ : ℕ}

open Classical in
/-- The decoder of a binning: the unique allowed sequence of the bin, and `d` if there is none. -/
private def binDec (B : (Fin n → α) → Fin M₁) (S : Fin M₂ → Finset (Fin n → α)) (d : Fin n → α)
    (w : Fin M₁ × Fin M₂) : Fin n → α :=
  if h : ∃ x, x ∈ S w.2 ∧ B x = w.1 ∧ ∀ x' ∈ S w.2, B x' = w.1 → x' = x then h.choose else d

open Classical in
private lemma binDec_ne_le (B : (Fin n → α) → Fin M₁) (S : Fin M₂ → Finset (Fin n → α))
    (d : Fin n → α) (x : Fin n → α) (m : Fin M₂) :
    (if binDec B S d (B x, m) ≠ x then (1 : ℝ) else 0) ≤
      (if x ∉ S m then 1 else 0) + ∑ x' ∈ (S m).erase x, if B x' = B x then 1 else 0 := by
  have hn0 : (0 : ℝ) ≤ ∑ x' ∈ (S m).erase x, if B x' = B x then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hx : x ∈ S m
  · by_cases hu : ∀ x' ∈ S m, B x' = B x → x' = x
    · have hex : ∃ x₀, x₀ ∈ S m ∧ B x₀ = B x ∧ ∀ x' ∈ S m, B x' = B x → x' = x₀ :=
        ⟨x, hx, rfl, hu⟩
      have hd : binDec B S d (B x, m) = x := by
        simp only [binDec]
        split
        · rename_i h
          exact hu _ h.choose_spec.1 h.choose_spec.2.1
        · contradiction
      simp only [hd, ne_eq, not_true_eq_false, ite_false, hx, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨x', hx', hb, hne⟩ := hu
      have h1 : (1 : ℝ) ≤ ∑ x' ∈ (S m).erase x, if B x' = B x then (1 : ℝ) else 0 := by
        have := single_le_sum (f := fun x' => if B x' = B x then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) (mem_erase.2 ⟨hne, hx'⟩)
        simpa [hb] using this
      split_ifs <;> linarith
  · simp only [hx, not_false_eq_true, ite_true]
    split_ifs <;> linarith

open Classical in
/-- **Lecture 11, pages 11-13, 11-14 and 11-28.** Random binning: for a helper encoder and sets
`S m` of at most `K` allowed sequences for each helper index `m`, there is a binning of the source
whose probability of error is at most `P{Xⁿ ∉ S(M₂)} + K / M₁`. -/
theorem exists_bins_code {q : α × β → ℝ} (hM₁ : 0 < M₁) (hq0 : ∀ z, 0 ≤ q z)
    (hq1 : ∑ z : (Fin n → α) × (Fin n → β), jointIid q n z = 1) (enc₂ : (Fin n → β) → Fin M₂)
    (S : Fin M₂ → Finset (Fin n → α)) (d : Fin n → α) {K : ℝ}
    (hK : ∀ m, ((S m).card : ℝ) ≤ K) :
    ∃ c : HelperCode M₁ M₂ n α β, c.enc₂ = enc₂ ∧ c.errProb q ≤
      (∑ z : (Fin n → α) × (Fin n → β), if z.1 ∉ S (enc₂ z.2) then jointIid q n z else 0) +
        K / M₁ := by
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  set N := Fintype.card (Fin n → α)
  set e : (Fin n → α) ≃ Fin N := Fintype.equivFin _
  set law : (Fin N → Fin M₁) → ℝ := iidPMF (uniformPMF (Fin M₁)) N with hlaw
  have hlawP : IsPMF law := iidPMF_isPMF uniformPMF_isPMF N
  have hM₁' : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  let code : (Fin N → Fin M₁) → HelperCode M₁ M₂ n α β := fun B =>
    ⟨fun x => B (e x), enc₂, binDec (fun x => B (e x)) S d⟩
  have hμ : ∀ z : (Fin n → α) × (Fin n → β), 0 ≤ jointIid q n z := jointIid_nonneg hq0 n
  -- The average over the binnings.
  have hpair : ∀ x x' : Fin n → α, x' ≠ x →
      ∑ B, law B * (if B (e x') = B (e x) then (1 : ℝ) else 0) = 1 / M₁ := fun x x' h =>
    sum_bins_eq_eq hM₁ (fun hh => h (e.injective hh.symm))
  have hsum : ∀ z : (Fin n → α) × (Fin n → β), ∑ B, law B *
      (if binDec (fun x => B (e x)) S d (B (e z.1), enc₂ z.2) ≠ z.1 then (1 : ℝ) else 0) ≤
      (if z.1 ∉ S (enc₂ z.2) then 1 else 0) + K / M₁ := fun z => by
    calc ∑ B, law B *
        (if binDec (fun x => B (e x)) S d (B (e z.1), enc₂ z.2) ≠ z.1 then (1 : ℝ) else 0)
        ≤ ∑ B, law B * ((if z.1 ∉ S (enc₂ z.2) then 1 else 0) +
            ∑ x' ∈ (S (enc₂ z.2)).erase z.1, if B (e x') = B (e z.1) then 1 else 0) :=
          sum_le_sum fun B _ => mul_le_mul_of_nonneg_left
            (binDec_ne_le (fun x => B (e x)) S d z.1 (enc₂ z.2)) (hlawP.nonneg B)
      _ = (if z.1 ∉ S (enc₂ z.2) then 1 else 0) +
            ∑ x' ∈ (S (enc₂ z.2)).erase z.1, ∑ B, law B *
              (if B (e x') = B (e z.1) then (1 : ℝ) else 0) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hlawP.sum_eq_one, one_mul]
          congr 1
          simp only [mul_sum]
          exact sum_comm
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [sum_congr rfl fun x' hx' => hpair z.1 x' (mem_erase.1 hx').1, sum_const,
            nsmul_eq_mul, mul_one_div]
          refine div_le_div_of_nonneg_right ?_ hM₁'.le
          have h1 : (((S (enc₂ z.2)).erase z.1).card : ℝ) ≤ (S (enc₂ z.2)).card := by
            exact_mod_cast card_erase_le
          exact h1.trans (hK _)
  have havg : ∑ B, law B * (code B).errProb q ≤
      (∑ z : (Fin n → α) × (Fin n → β), if z.1 ∉ S (enc₂ z.2) then jointIid q n z else 0) +
        K / M₁ := by
    have e1 : ∀ B, law B * (code B).errProb q = ∑ z, jointIid q n z * (law B *
        (if binDec (fun x => B (e x)) S d (B (e z.1), enc₂ z.2) ≠ z.1 then (1 : ℝ) else 0)) :=
      fun B => by
        simp only [code, HelperCode.errProb, mul_sum]
        refine sum_congr rfl fun z _ => ?_
        split_ifs <;> ring
    simp only [e1]
    rw [sum_comm]
    calc ∑ z, ∑ B, jointIid q n z * (law B *
        (if binDec (fun x => B (e x)) S d (B (e z.1), enc₂ z.2) ≠ z.1 then (1 : ℝ) else 0))
        = ∑ z, jointIid q n z * ∑ B, law B *
          (if binDec (fun x => B (e x)) S d (B (e z.1), enc₂ z.2) ≠ z.1 then (1 : ℝ) else 0) :=
          sum_congr rfl fun z _ => (mul_sum _ _ _).symm
      _ ≤ ∑ z, jointIid q n z * ((if z.1 ∉ S (enc₂ z.2) then 1 else 0) + K / M₁) :=
          sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hsum z) (hμ z)
      _ = _ := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hq1, one_mul]
          congr 1
          refine sum_congr rfl fun z _ => ?_
          split_ifs <;> simp
  obtain ⟨B, hB⟩ := exists_le_of_sum_mul_le hlawP havg
  exact ⟨code B, rfl, hB⟩

end Binning

/-! ### Covering and conditional typicality -/

section Covering

variable {q : α × β → ℝ} {κ : β → 𝒰 → ℝ} {n : ℕ}

/-- The law of `((Y, U), X)`. -/
def helperTriple (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) : (β × 𝒰) × α → ℝ :=
  fun z => helperLaw q κ ((z.2, z.1.1), z.1.2)

/-- The law of `(U, X)`. -/
def helperUX (q : α × β → ℝ) (κ : β → 𝒰 → ℝ) : 𝒰 × α → ℝ :=
  dist (helperTriple q κ) fun z => (z.1.2, z.2)

/-- The rearrangement of `((Y, U), X)` as `((X, Y), U)`. -/
private def helperEquiv : (β × 𝒰) × α ≃ (α × β) × 𝒰 where
  toFun z := ((z.2, z.1.1), z.1.2)
  invFun z := ((z.1.2, z.2), z.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

lemma helperTriple_isPMF (hq : IsPMF q) (hκ : ∀ y, IsPMF (κ y)) : IsPMF (helperTriple q κ) := by
  have h := helperLaw_isPMF hq hκ
  refine ⟨fun z => h.nonneg _, ?_⟩
  rw [← h.sum_eq_one]
  exact helperEquiv.sum_comp (helperLaw q κ)

lemma helperUX_isPMF (hq : IsPMF q) (hκ : ∀ y, IsPMF (κ y)) : IsPMF (helperUX q κ) :=
  (helperTriple_isPMF hq hκ).dist _

omit [Fintype 𝒰] in
/-- `p(y, u) = p(y) p(u | y)`. -/
lemma marg_helperTriple (y : β) (u : 𝒰) :
    marg (helperTriple q κ) (y, u) = margSnd q y * κ y u := by
  simp only [marg, helperTriple, helperLaw, jointOf]
  rw [← sum_mul, show margSnd q y = ∑ a, q (a, y) from dist_snd q y]

/-- `p(y) = ∑ᵤ p(y, u)`. -/
lemma margFst_margFst_helperTriple (hκ : ∀ y, IsPMF (κ y)) :
    margFst (margFst (helperTriple q κ)) = margSnd q := by
  funext y
  have e : ∀ u, margFst (helperTriple q κ) (y, u) = margSnd q y * κ y u := fun u => by
    rw [show margFst (helperTriple q κ) (y, u) = ∑ a, helperTriple q κ ((y, u), a) from
      dist_fst _ _]
    simp only [helperTriple, helperLaw, jointOf]
    rw [← sum_mul, show margSnd q y = ∑ a, q (a, y) from dist_snd q y]
  rw [show margFst (margFst (helperTriple q κ)) y = ∑ u, margFst (helperTriple q κ) (y, u) from
    dist_fst _ _]
  simp only [e, ← mul_sum, (hκ y).sum_eq_one, mul_one]

private lemma dist_helperEquiv {γ : Type*} (q : α × β → ℝ) (κ : β → 𝒰 → ℝ)
    (f : (α × β) × 𝒰 → γ) (a : γ) :
    dist (helperTriple q κ) (fun z => f (helperEquiv z)) a = dist (helperLaw q κ) f a := by
  classical
  simp only [dist]
  exact Equiv.sum_comp helperEquiv fun z => if f z = a then helperLaw q κ z else 0

/-- `H(X | U)` is the conditional entropy under the law of `(U, X)`. -/
lemma helperCond_eq (hq : IsPMF q) (hκ : ∀ y, IsPMF (κ y)) :
    helperCond q κ = H[Prod.snd | Prod.fst ; helperUX q κ] := by
  classical
  refine condEntropy_eq_of_dist_pair_eq (helperLaw_isPMF hq hκ) (helperUX_isPMF hq hκ) ?_
  rw [dist_pair_fst_snd]
  funext ⟨u, x⟩
  exact (dist_helperEquiv q κ (pair Prod.snd fun z => z.1.1) (u, x)).symm

/-- `I(Y; U)` is the mutual information under the law of `(Y, U)`. -/
lemma helperInfo_eq :
    helperInfo q κ = I[Prod.fst : Prod.snd ; margFst (helperTriple q κ)] := by
  classical
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [dist_pair_fst_snd]
  funext ⟨y, u⟩
  exact (dist_helperEquiv q κ (pair (fun z => z.1.2) Prod.snd) (y, u)).symm

omit [Fintype β] [Fintype 𝒰] in
/-- A sequence typical with `(yⁿ, uⁿ)` under `p(y, u, x)` is typical with `uⁿ`. -/
private lemma mem_condRobust_helperUX [Fintype β] [Fintype 𝒰] {ε : ℝ} {y : Fin n → β}
    {u : Fin n → 𝒰} {x : Fin n → α}
    (h : x ∈ condRobustTypicalSet (helperTriple q κ) ε (zipSeq y u)) :
    x ∈ condRobustTypicalSet (helperUX q κ) ε u := by
  rw [mem_condRobustTypicalSet] at h ⊢
  exact comp_mem_robustTypicalSet h fun z => (z.1.2, z.2)

open Classical in
/-- **Lecture 11, page 11-27.** If `(yⁿ, uⁿ)` is typical then, by the conditional typicality lemma
for the Markov chain `U → Y → X`, so is `(uⁿ, Xⁿ)` for `Xⁿ` given `yⁿ`, up to `K / n`. -/
theorem sum_jointIid_not_mem_le (hq : IsPMF q) (hκ : ∀ y, IsPMF (κ y)) {ε' ε : ℝ} (hεε : ε' < ε)
    (hn : 0 < n) {y : Fin n → β} {u : Fin n → 𝒰}
    (hyu : zipSeq y u ∈ robustTypicalSet (margFst (helperTriple q κ)) n ε') :
    ∑ x, (if x ∉ condRobustTypicalSet (helperUX q κ) ε u then jointIid q n (x, y) else 0) ≤
      iidPMF (margSnd q) n y * (condTypicalityConst (helperTriple q κ) ε' ε / n) := by
  have ht := helperTriple_isPMF hq hκ
  set t := helperTriple q κ with htd
  have hpy0 : ∀ b, 0 ≤ margSnd q b := (hq.dist Prod.snd).nonneg
  have hpos : ∀ i, 0 < marg t (y i, u i) := fun i => by
    have h := pos_of_mem_robustTypicalSet ((ht.dist Prod.fst).nonneg) hyu i
    rwa [marg_eq_dist]
  have hcoord : ∀ i (a : α), q (a, y i) = margSnd q (y i) * condPMF t (y i, u i) a := fun i a => by
    have hm : marg t (y i, u i) = margSnd q (y i) * κ (y i) (u i) := marg_helperTriple _ _
    have hp := hpos i
    rw [hm] at hp
    have hκne : κ (y i) (u i) ≠ 0 := fun h => by simp [h] at hp
    have hpne : margSnd q (y i) ≠ 0 := fun h => by simp [h] at hp
    rw [condPMF, hm]
    simp only [htd, helperTriple, helperLaw, jointOf]
    field_simp
  have hfac : ∀ x : Fin n → α, jointIid q n (x, y) =
      iidPMF (margSnd q) n y * channelExt (condPMF t) n (zipSeq y u) x := fun x => by
    simp only [jointIid, iidPMF, channelExt, zipSeq]
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ => hcoord i (x i)
  have hch0 : ∀ x, 0 ≤ channelExt (condPMF t) n (zipSeq y u) x := fun x =>
    prod_nonneg fun i _ => condPMF_nonneg ht.nonneg _ _
  have hiid0 : 0 ≤ iidPMF (margSnd q) n y := iidPMF_nonneg hpy0 y
  have hc := one_sub_div_le_prob_condRobustTypicalSet ht hεε hn hyu
  have hsum := sum_channelExt_condPMF_le_one ht.nonneg (zipSeq y u)
  -- The mass off the conditionally typical set.
  have hoff : ∑ x, (if x ∉ condRobustTypicalSet t ε (zipSeq y u) then
      channelExt (condPMF t) n (zipSeq y u) x else 0) ≤ condTypicalityConst t ε' ε / n := by
    have hsplit : ∑ x, (if x ∉ condRobustTypicalSet t ε (zipSeq y u) then
        channelExt (condPMF t) n (zipSeq y u) x else 0) =
        ∑ x, channelExt (condPMF t) n (zipSeq y u) x -
          prob (channelExt (condPMF t) n (zipSeq y u)) (condRobustTypicalSet t ε (zipSeq y u)) := by
      rw [prob, ← sum_filter_add_sum_filter_not univ
        (fun x => x ∈ condRobustTypicalSet t ε (zipSeq y u))
        fun x => channelExt (condPMF t) n (zipSeq y u) x, filter_mem_eq_inter, univ_inter,
        add_sub_cancel_left, sum_filter]
    rw [hsplit]
    linarith
  calc ∑ x, (if x ∉ condRobustTypicalSet (helperUX q κ) ε u then jointIid q n (x, y) else 0)
      ≤ ∑ x, iidPMF (margSnd q) n y * (if x ∉ condRobustTypicalSet t ε (zipSeq y u) then
          channelExt (condPMF t) n (zipSeq y u) x else 0) := by
        refine sum_le_sum fun x _ => ?_
        rw [hfac x]
        by_cases h1 : x ∈ condRobustTypicalSet t ε (zipSeq y u)
        · have h2 := mem_condRobust_helperUX h1
          simp [h1, h2]
        · by_cases h2 : x ∈ condRobustTypicalSet (helperUX q κ) ε u
          · simp only [h2, h1, not_true_eq_false, not_false_eq_true, ite_false, ite_true]
            exact mul_nonneg hiid0 (hch0 x)
          · simp [h1, h2]
    _ = iidPMF (margSnd q) n y * ∑ x, (if x ∉ condRobustTypicalSet t ε (zipSeq y u) then
          channelExt (condPMF t) n (zipSeq y u) x else 0) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hoff hiid0

open Classical in
/-- The helper encoder of a codebook: a sequence of the codebook typical with `yⁿ`. -/
def helperEnc {L : ℕ} (hL : 0 < L) (T : Finset (Fin n → β × 𝒰)) (C : Fin L → Fin n → 𝒰)
    (y : Fin n → β) : Fin L :=
  if h : ∃ m, zipSeq y (C m) ∈ T then h.choose else ⟨0, hL⟩

open Classical in
/-- **Lecture 11, page 11-27.** For a fixed codebook: the error events `E₁` and `E₂`. -/
theorem sum_not_mem_helperEnc_le (hq : IsPMF q) (hκ : ∀ y, IsPMF (κ y)) {ε' ε : ℝ} (hεε : ε' < ε)
    (hn : 0 < n) {L : ℕ} (hL : 0 < L) (C : Fin L → Fin n → 𝒰) :
    (∑ z : (Fin n → α) × (Fin n → β), if z.1 ∉ condRobustTypicalSet (helperUX q κ) ε
        (C (helperEnc hL (robustTypicalSet (margFst (helperTriple q κ)) n ε') C z.2)) then
        jointIid q n z else 0) ≤
      ∑ y, iidPMF (margSnd q) n y * (if ∀ m, zipSeq y (C m) ∉
        robustTypicalSet (margFst (helperTriple q κ)) n ε' then 1 else 0) +
      condTypicalityConst (helperTriple q κ) ε' ε / n := by
  have hpy0 : ∀ b, 0 ≤ margSnd q b := (hq.dist Prod.snd).nonneg
  set T := robustTypicalSet (margFst (helperTriple q κ)) n ε'
  set K := condTypicalityConst (helperTriple q κ) ε' ε / n
  have hK0 : 0 ≤ K := by
    refine div_nonneg (sum_nonneg fun z _ => ?_) (Nat.cast_nonneg n)
    positivity
  have hy : ∀ y, ∑ x, (if x ∉ condRobustTypicalSet (helperUX q κ) ε (C (helperEnc hL T C y)) then
      jointIid q n (x, y) else 0) ≤ iidPMF (margSnd q) n y *
        (if ∀ m, zipSeq y (C m) ∉ T then 1 else 0) + iidPMF (margSnd q) n y * K := fun y => by
    have h0 := iidPMF_nonneg hpy0 y (n := n)
    by_cases hm : ∃ m, zipSeq y (C m) ∈ T
    · have hspec : zipSeq y (C (helperEnc hL T C y)) ∈ T := by
        simp only [helperEnc]
        split
        · rename_i h
          exact h.choose_spec
        · contradiction
      have hnot : ¬ ∀ m, zipSeq y (C m) ∉ T := by
        push Not
        exact hm
      have e : (if ∀ m, zipSeq y (C m) ∉ T then (1 : ℝ) else 0) = 0 := by
        split_ifs
        rfl
      rw [e, mul_zero, zero_add]
      exact sum_jointIid_not_mem_le hq hκ hεε hn hspec
    · have hall : ∀ m, zipSeq y (C m) ∉ T := fun m h => hm ⟨m, h⟩
      have e : (if ∀ m, zipSeq y (C m) ∉ T then (1 : ℝ) else 0) = 1 := by
        split_ifs
        rfl
      rw [e, mul_one]
      calc ∑ x, (if x ∉ condRobustTypicalSet (helperUX q κ) ε (C (helperEnc hL T C y)) then
          jointIid q n (x, y) else 0) ≤ ∑ x, jointIid q n (x, y) :=
            sum_le_sum fun x _ => by
              split_ifs
              · exact jointIid_nonneg hq.nonneg n _
              · exact le_rfl
        _ = iidPMF (margSnd q) n y := sum_jointIid_fiber_fst q n y
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg h0 hK0)
  rw [Fintype.sum_prod_type_right]
  refine (sum_le_sum fun y _ => hy y).trans (le_of_eq ?_)
  rw [sum_add_distrib, ← sum_mul, (iidPMF_isPMF (hq.dist Prod.snd) n).sum_eq_one, one_mul]

/-- **Lecture 11, pages 11-27 and 11-28.** The bound on the probability of error: for `n` large and
any numbers of indices, there is a code with
`P_e ≤ P{Yⁿ ∉ T_{ε''}} + exp(-L (1 - ε') e^{-n(I(Y; U) + δ')}) + K / n + e^{n(H(X | U) + δ)} / M₁`.
-/
theorem exists_helper_code_le (hq : IsPMF q) (hκ : ∀ y, IsPMF (κ y)) {ε'' ε' ε : ℝ}
    (hε'' : ε'' < ε') (hε' : 0 < ε') (hεε : ε' < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ {M₁ L : ℕ}, 0 < M₁ → 0 < L → ∃ c : HelperCode M₁ L n α β,
      c.errProb q ≤ (1 - prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n ε'')) +
        exp (-(L * ((1 - ε') * exp (-(n * (I[Prod.snd : Prod.fst ; margFst (helperTriple q κ)] +
          ε' * (H[Prod.snd ; margFst (helperTriple q κ)] +
            H[Prod.snd | Prod.fst ; margFst (helperTriple q κ)]))))))) +
        condTypicalityConst (helperTriple q κ) ε' ε / n +
        exp (n * (H[Prod.snd | Prod.fst ; helperUX q κ] +
          ε * H[Prod.snd | Prod.fst ; helperUX q κ])) / M₁ := by
  classical
  have hne : Nonempty (α × β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  obtain ⟨⟨a, b⟩⟩ := hne
  have ht := helperTriple_isPMF hq hκ
  have hq₀ := ht.dist (Prod.fst : (β × 𝒰) × α → β × 𝒰)
  have hpY := hq.dist (Prod.snd : α × β → β)
  have hUX := helperUX_isPMF hq hκ
  set q₀ := margFst (helperTriple q κ) with hq₀d
  have hm : margFst q₀ = margSnd q := margFst_margFst_helperTriple hκ
  filter_upwards [eventually_le_prob_iidPMF_condRobustTypicalSet hq₀ hε'' hε',
    eventually_gt_atTop 0] with n hcov hn M₁ L hM₁ hL
  rw [hm] at hcov
  have hpU := hq₀.dist (Prod.snd : β × 𝒰 → 𝒰)
  set pU := margSnd q₀
  set law := iidPMF (iidPMF pU n) L with hlaw
  have hlawP : IsPMF law := iidPMF_isPMF (iidPMF_isPMF hpU n) L
  set T := robustTypicalSet q₀ n ε'
  set low := (1 - ε') * exp (-(n * (I[Prod.snd : Prod.fst ; q₀] +
    ε' * (H[Prod.snd ; q₀] + H[Prod.snd | Prod.fst ; q₀]))))
  -- The average over the codebooks of the covering failure.
  have hcover : ∑ C, law C * ∑ y, iidPMF (margSnd q) n y *
      (if ∀ m, zipSeq y (C m) ∉ T then 1 else 0) ≤
      (1 - prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n ε'')) +
        exp (-(L * low)) := by
    have hswap : ∑ C, law C * ∑ y, iidPMF (margSnd q) n y *
        (if ∀ m, zipSeq y (C m) ∉ T then (1 : ℝ) else 0) = ∑ y, iidPMF (margSnd q) n y *
          ∑ C, law C * (if ∀ m, zipSeq y (C m) ∉ T then (1 : ℝ) else 0) := by
      simp only [mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun y _ => sum_congr rfl fun C _ => by ring
    have hin : ∀ y, ∑ C, law C * (if ∀ m, zipSeq y (C m) ∉ T then (1 : ℝ) else 0) ≤
        exp (-(L * prob (iidPMF pU n) (condRobustTypicalSet q₀ ε' y))) := fun y => by
      have h := sum_iidPMF_ite_forall_not_mem_le (iidPMF_isPMF hpU n) L
        (condRobustTypicalSet q₀ ε' y)
      refine le_of_eq_of_le (sum_congr rfl fun C _ => ?_) h
      congr 2
      simp only [mem_condRobustTypicalSet]
      rfl
    have hbd : ∀ y, ∑ C, law C * (if ∀ m, zipSeq y (C m) ∉ T then (1 : ℝ) else 0) ≤
        (if y ∈ robustTypicalSet (margSnd q) n ε'' then exp (-(L * low)) else 1) := fun y => by
      split_ifs with hy
      · refine (hin y).trans (exp_le_exp.2 ?_)
        have := hcov y hy
        have hL' : (0 : ℝ) ≤ L := Nat.cast_nonneg L
        nlinarith
      · refine (sum_le_sum fun C _ => ?_).trans hlawP.sum_eq_one.le
        refine mul_le_of_le_one_right (hlawP.nonneg C) ?_
        split_ifs <;> norm_num
    rw [hswap]
    have hp0 := iidPMF_nonneg hpY.nonneg (n := n)
    have hpr : prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n ε'') =
        ∑ y, if y ∈ robustTypicalSet (margSnd q) n ε'' then iidPMF (margSnd q) n y else 0 := by
      rw [sum_ite_mem, univ_inter]
      rfl
    calc ∑ y, iidPMF (margSnd q) n y * ∑ C, law C *
        (if ∀ m, zipSeq y (C m) ∉ T then (1 : ℝ) else 0)
        ≤ ∑ y, iidPMF (margSnd q) n y *
          (if y ∈ robustTypicalSet (margSnd q) n ε'' then exp (-(L * low)) else 1) :=
          sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hbd y) (hp0 y)
      _ ≤ _ := by
          have hsplit : ∑ y, iidPMF (margSnd q) n y *
              (if y ∈ robustTypicalSet (margSnd q) n ε'' then exp (-(L * low)) else 1) =
              prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n ε'') *
                  exp (-(L * low)) +
                (1 - prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n ε'')) := by
            have h1 := (iidPMF_isPMF hpY n).sum_eq_one
            have h4 : 1 - ∑ y, (if y ∈ robustTypicalSet (margSnd q) n ε'' then
                iidPMF (margSnd q) n y else 0) = ∑ y, (iidPMF (margSnd q) n y -
                  if y ∈ robustTypicalSet (margSnd q) n ε'' then
                    iidPMF (margSnd q) n y else 0) := by
              rw [sum_sub_distrib, h1]
            rw [hpr, sum_mul, h4, ← sum_add_distrib]
            refine sum_congr rfl fun y _ => ?_
            split_ifs <;> ring
          rw [hsplit]
          have h2 := prob_le_one (iidPMF_isPMF hpY n) (robustTypicalSet (margSnd q) n ε'')
          have h3 := exp_pos (-(L * low))
          nlinarith
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hlawP hcover
  set enc₂ := helperEnc hL T C
  have hcard : ∀ m, ((condRobustTypicalSet (helperUX q κ) ε (C m)).card : ℝ) ≤
      exp (n * (H[Prod.snd | Prod.fst ; helperUX q κ] +
        ε * H[Prod.snd | Prod.fst ; helperUX q κ])) := fun m =>
    card_condRobustTypicalSet_le hUX ε (C m)
  obtain ⟨c, -, hc⟩ := exists_bins_code (q := q) hM₁ hq.nonneg (jointIid_isPMF hq n).sum_eq_one enc₂
    (fun m => condRobustTypicalSet (helperUX q κ) ε (C m)) (fun _ => a) hcard
  refine ⟨c, hc.trans ?_⟩
  have hB := sum_not_mem_helperEnc_le hq hκ hεε hn hL C
  refine add_le_add ((le_of_eq_of_le ?_ hB).trans ?_) le_rfl
  · rfl
  · linarith

end Covering

/-! ### Rates -/

section Rates

variable {q : α × β → ℝ}

omit [Fintype α] [Fintype β] [Fintype 𝒰] in
private lemma two_mul_exp_eq (a : ℝ) : 2 * exp a = exp (a + log 2) := by
  rw [exp_add, exp_log two_pos]
  ring

/-- **Theorem 2 of Lecture 11, achievability.** Rates with `R₁ > H(X | U)` and `R₂ > I(Y; U)` for
some `p(u | y)` are achievable. -/
theorem isAchievableHelperBits_of_lt (hq : IsPMF q) {κ : β → 𝒰 → ℝ} (hκ : ∀ y, IsPMF (κ y))
    {R₁ R₂ : ℝ} (h₁ : helperCond q κ / log 2 < R₁) (h₂ : helperInfo q κ / log 2 < R₂) :
    IsAchievableHelperBits q R₁ R₂ := by
  classical
  have hl := log_pos one_lt_two
  have hne : Nonempty (α × β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  obtain ⟨⟨a, b⟩⟩ := hne
  have ht := helperTriple_isPMF hq hκ
  have hUX := helperUX_isPMF hq hκ
  have hq₀ := ht.dist (Prod.fst : (β × 𝒰) × α → β × 𝒰)
  have hpY := hq.dist (Prod.snd : α × β → β)
  rw [helperCond_eq hq hκ] at h₁
  rw [helperInfo_eq] at h₂
  set Hc := H[Prod.snd | Prod.fst ; helperUX q κ] with hHc
  set q₀ := margFst (helperTriple q κ) with hq₀d
  have hI' : I[Prod.snd : Prod.fst ; q₀] = I[Prod.fst : Prod.snd ; q₀] := mutualInfo_comm hq₀ _ _
  set I₀ := I[Prod.fst : Prod.snd ; q₀] with hI₀
  set D := H[Prod.snd ; q₀] + H[Prod.snd | Prod.fst ; q₀] with hD
  have hHc0 : 0 ≤ Hc := condEntropy_nonneg hUX _ _
  have hD0 : 0 ≤ D := add_nonneg (entropy_nonneg (hq₀.dist _)) (condEntropy_nonneg hq₀ _ _)
  have hI0 : 0 ≤ I₀ := mutualInfo_nonneg hq₀ _ _
  have g₁ : Hc < R₁ * log 2 := (div_lt_iff₀ hl).1 h₁
  have g₂ : I₀ < R₂ * log 2 := (div_lt_iff₀ hl).1 h₂
  have hR₁ : 0 ≤ R₁ := (div_nonneg hHc0 hl.le).trans h₁.le
  have hR₂ : 0 ≤ R₂ := (div_nonneg hI0 hl.le).trans h₂.le
  -- The choice of `ε`.
  obtain ⟨ε, hε, hε1, e₁, e₂⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ Hc + ε * Hc < R₁ * log 2 ∧
      I₀ + ε / 2 * D < R₂ * log 2 := by
    refine ⟨min 1 (min ((R₁ * log 2 - Hc) / (2 * (Hc + 1))) ((R₂ * log 2 - I₀) / (D + 1))),
      lt_min one_pos (lt_min (div_pos (by linarith) (by positivity))
        (div_pos (by linarith) (by positivity))), min_le_left _ _, ?_, ?_⟩
    · have h3 : min 1 (min ((R₁ * log 2 - Hc) / (2 * (Hc + 1))) ((R₂ * log 2 - I₀) / (D + 1))) ≤
          (R₁ * log 2 - Hc) / (2 * (Hc + 1)) :=
        (min_le_right _ _).trans (min_le_left _ _)
      have h4 : min 1 (min ((R₁ * log 2 - Hc) / (2 * (Hc + 1))) ((R₂ * log 2 - I₀) / (D + 1))) *
          Hc ≤ (R₁ * log 2 - Hc) / (2 * (Hc + 1)) * Hc := mul_le_mul_of_nonneg_right h3 hHc0
      have h5 : (R₁ * log 2 - Hc) / (2 * (Hc + 1)) * Hc ≤ (R₁ * log 2 - Hc) / 2 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    · have h3 : min 1 (min ((R₁ * log 2 - Hc) / (2 * (Hc + 1))) ((R₂ * log 2 - I₀) / (D + 1))) ≤
          (R₂ * log 2 - I₀) / (D + 1) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have h4 : min 1 (min ((R₁ * log 2 - Hc) / (2 * (Hc + 1))) ((R₂ * log 2 - I₀) / (D + 1))) /
          2 * D ≤ (R₂ * log 2 - I₀) / (D + 1) / 2 * D :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h3 (by norm_num)) hD0
      have h5 : (R₂ * log 2 - I₀) / (D + 1) / 2 * D ≤ (R₂ * log 2 - I₀) / 2 := by
        rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
  have hε' : 0 < ε / 2 := half_pos hε
  have hε'1 : 0 < 1 - ε / 2 := by linarith
  set G₁ := R₁ * log 2 - (Hc + ε * Hc) with hG₁
  set G₂ := R₂ * log 2 - (I₀ + ε / 2 * D) with hG₂
  have hG₁0 : 0 < G₁ := by linarith
  have hG₂0 : 0 < G₂ := by linarith
  -- The bound and its limit.
  have hcode := exists_helper_code_le hq hκ (ε'' := ε / 4) (ε' := ε / 2) (ε := ε) (by linarith)
    hε' (by linarith)
  set P : ℕ → ℝ := fun n =>
    (1 - prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n (ε / 4))) +
      exp (-(1 / 2 * (1 - ε / 2) * exp (n * G₂))) +
      condTypicalityConst (helperTriple q κ) (ε / 2) ε / n + 2 * exp (-(n * G₁)) with hP
  have hPlim : Tendsto P atTop (𝓝 0) := by
    have t₁ : Tendsto (fun n => 1 - prob (iidPMF (margSnd q) n)
        (robustTypicalSet (margSnd q) n (ε / 4))) atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet hpY (by linarith : 0 < ε / 4)).const_sub 1
    have t₂ : Tendsto (fun n : ℕ => exp (-(1 / 2 * (1 - ε / 2) * exp (n * G₂)))) atTop (𝓝 0) := by
      refine tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop (by positivity) ?_)
      exact tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const hG₂0)
    have t₃ : Tendsto (fun n : ℕ => condTypicalityConst (helperTriple q κ) (ε / 2) ε / n) atTop
        (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    have t₄ : Tendsto (fun n : ℕ => 2 * exp (-(n * G₁))) atTop (𝓝 0) := by
      simpa using (tendsto_exp_neg_mul_nat hG₁0).const_mul 2
    simpa [P] using ((t₁.add t₂).add t₃).add t₄
  have hsub : ∀ n : ℕ, ∃ c : HelperCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β,
      (∀ {M₁ L : ℕ}, 0 < M₁ → 0 < L → ∃ c : HelperCode M₁ L n α β,
        c.errProb q ≤ (1 - prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n (ε / 4))) +
        exp (-(L * ((1 - ε / 2) * exp (-(n * (I[Prod.snd : Prod.fst ; q₀] +
          ε / 2 * D)))))) +
        condTypicalityConst (helperTriple q κ) (ε / 2) ε / n +
        exp (n * (Hc + ε * Hc)) / M₁) → c.errProb q ≤ P n := fun n => by
    by_cases hn : ∀ {M₁ L : ℕ}, 0 < M₁ → 0 < L → ∃ c : HelperCode M₁ L n α β,
        c.errProb q ≤ (1 - prob (iidPMF (margSnd q) n) (robustTypicalSet (margSnd q) n (ε / 4))) +
        exp (-(L * ((1 - ε / 2) * exp (-(n * (I[Prod.snd : Prod.fst ; q₀] +
          ε / 2 * D)))))) +
        condTypicalityConst (helperTriple q κ) (ε / 2) ε / n +
        exp (n * (Hc + ε * Hc)) / M₁
    · obtain ⟨c, hc⟩ := hn (M₁ := 2 ^ ⌊n * R₁⌋₊) (L := 2 ^ ⌊n * R₂⌋₊) (by positivity)
        (by positivity)
      refine ⟨c, fun _ => hc.trans ?_⟩
      have hLb := exp_le_two_pow_floor n R₂
      have hMb := exp_le_two_pow_floor n R₁
      rw [hI']
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      -- The covering term.
      have hcov : exp (-(((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ) * ((1 - ε / 2) *
          exp (-(n * (I₀ + ε / 2 * D)))))) ≤ exp (-(1 / 2 * (1 - ε / 2) * exp (n * G₂))) := by
        refine exp_le_exp.2 (neg_le_neg ?_)
        have h1 : exp (n * G₂) = 2 * (exp (n * (R₂ * log 2) - log 2) *
            exp (-(n * (I₀ + ε / 2 * D)))) := by
          rw [← exp_add, two_mul_exp_eq]
          congr 1
          simp only [hG₂]
          ring
        have h2 : exp (n * (R₂ * log 2) - log 2) * exp (-(n * (I₀ + ε / 2 * D))) ≤
            ((2 ^ ⌊n * R₂⌋₊ : ℕ) : ℝ) * exp (-(n * (I₀ + ε / 2 * D))) :=
          mul_le_mul_of_nonneg_right hLb (exp_pos _).le
        rw [h1]
        have h3 : 0 < 1 - ε / 2 := hε'1
        nlinarith [mul_le_mul_of_nonneg_left h2 h3.le]
      -- The binning term.
      have hbin : exp (n * (Hc + ε * Hc)) / ((2 ^ ⌊n * R₁⌋₊ : ℕ) : ℝ) ≤ 2 * exp (-(n * G₁)) := by
        have hpos : (0 : ℝ) < exp (n * (R₁ * log 2) - log 2) := exp_pos _
        refine (div_le_div_of_nonneg_left (exp_pos _).le hpos hMb).trans (le_of_eq ?_)
        rw [← exp_sub, two_mul_exp_eq]
        congr 1
        simp only [hG₁]
        ring
      simp only [P]
      linarith
    · exact ⟨⟨fun _ => ⟨0, by positivity⟩, fun _ => ⟨0, by positivity⟩, fun _ _ => a⟩,
        fun h' => absurd @h' hn⟩
  choose c hc using hsub
  refine ⟨hR₁, hR₂, c, tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hPlim
    (Eventually.of_forall fun n => (c n).errProb_nonneg hq) ?_⟩
  filter_upwards [hcode] with n hn
  exact hc n hn

end Rates

end InfoTheory
