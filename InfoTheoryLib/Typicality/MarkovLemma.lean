/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Typicality.Conditional

/-!
# The Markov lemma

Let `X → Y → Z` be a Markov chain, `(xⁿ, yⁿ)` be typical, and let `Zⁿ` be drawn from a law `φ` on
sequences that is not a product law, but is concentrated on the typical set `T(Z | yⁿ)` and assigns
to each of its sequences a mass of about `e^{-n H(Z | Y)}`. The Markov lemma says that
`(xⁿ, yⁿ, Zⁿ)` is typical with probability tending to `1`.

The notes prove it by comparing with a hypergeometric random variable. We use a change of measure
instead. On `T(Z | yⁿ)`, the law `φ` is within a factor `e^{2nδ}` of the product law
`∏ᵢ p(zᵢ | yᵢ)`, with `δ → 0` as the typicality parameter of `T(Z | yⁿ)` tends to `0`. By the
Chernoff bound, the product law gives probability at most `e^{-nc}` to the atypical sequences, with
`c` that depends only on the typicality parameters of `(xⁿ, yⁿ, Zⁿ)` and of `(xⁿ, yⁿ)`.

## Main statements

* `sum_prod_mul_exp_sum_le`, `sum_prod_abs_ge_le`: the Chernoff bound for independent bounded random
  variables of mean `0`.
* `one_sub_condExpBound_le_prob`: the conditional typicality lemma with an exponential bound.
* `sum_not_mem_condRobust_le`: **the Markov lemma**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 13
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-! ### The Chernoff bound -/

section Chernoff

variable {n : ℕ} {P f : Fin n → β → ℝ}

omit [Fintype α] [Fintype γ] in
/-- The moment generating function of a sum of independent bounded random variables of mean `0`. -/
theorem sum_prod_mul_exp_sum_le (hP : ∀ i, IsPMF (P i)) (hf0 : ∀ i, ∑ b, P i b * f i b = 0)
    (hf1 : ∀ i b, |f i b| ≤ 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∑ y : Fin n → β, (∏ i, P i (y i)) * exp (s * ∑ i, f i (y i)) ≤ exp (n * s ^ 2) := by
  have hprod : ∀ y : Fin n → β, exp (s * ∑ i, f i (y i)) = ∏ i, exp (s * f i (y i)) := fun y => by
    rw [mul_sum, exp_sum]
  simp only [hprod]
  rw [sum_prod_mul_prod P fun i b => exp (s * f i b)]
  have hone : ∀ i, ∑ b, P i b * exp (s * f i b) ≤ exp (s ^ 2) := fun i => by
    have hb : ∀ b, exp (s * f i b) ≤ 1 + s * f i b + s ^ 2 := fun b => by
      have habs : |s * f i b| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hs0]
        calc s * |f i b| ≤ 1 * 1 := mul_le_mul hs1 (hf1 i b) (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have h := abs_exp_sub_one_sub_id_le habs
      have h2 : (s * f i b) ^ 2 ≤ s ^ 2 := by
        rw [mul_pow]
        have : f i b ^ 2 ≤ 1 := by
          rw [← sq_abs]
          exact pow_le_one₀ (abs_nonneg _) (hf1 i b)
        nlinarith [sq_nonneg s]
      linarith [(abs_le.1 h).2]
    calc ∑ b, P i b * exp (s * f i b) ≤ ∑ b, P i b * (1 + s * f i b + s ^ 2) :=
          sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hb b) ((hP i).nonneg b)
      _ = 1 + s ^ 2 := by
          have e : ∀ b, P i b * (1 + s * f i b + s ^ 2) =
              P i b * (1 + s ^ 2) + s * (P i b * f i b) := fun b => by ring
          simp only [e, sum_add_distrib, ← sum_mul, ← mul_sum, (hP i).sum_eq_one, hf0 i]
          ring
      _ ≤ exp (s ^ 2) := by linarith [add_one_le_exp (s ^ 2)]
  have hn0 : ∀ i, 0 ≤ ∑ b, P i b * exp (s * f i b) := fun i =>
    sum_nonneg fun b _ => mul_nonneg ((hP i).nonneg b) (exp_pos _).le
  calc ∏ i, ∑ b, P i b * exp (s * f i b) ≤ ∏ _i : Fin n, exp (s ^ 2) :=
        prod_le_prod₀ (fun i _ => hn0 i) fun i _ => hone i
    _ = exp (n * s ^ 2) := by
        rw [prod_const, card_univ, Fintype.card_fin, ← exp_natCast_mul]

open Classical in
omit [Fintype α] [Fintype γ] in
/-- **The Chernoff bound.** For independent random variables of mean `0` bounded by `1` and
`0 < t ≤ 1`, `P{∑ᵢ fᵢ ≥ n t} ≤ e^{-n t² / 4}`. -/
theorem sum_prod_ge_le (hP : ∀ i, IsPMF (P i)) (hf0 : ∀ i, ∑ b, P i b * f i b = 0)
    (hf1 : ∀ i b, |f i b| ≤ 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∑ y : Fin n → β, (∏ i, P i (y i)) * (if n * t ≤ ∑ i, f i (y i) then 1 else 0) ≤
      exp (-(n * t ^ 2 / 4)) := by
  have hμ0 : ∀ y : Fin n → β, 0 ≤ ∏ i, P i (y i) := fun y =>
    prod_nonneg fun i _ => (hP i).nonneg _
  have hm := sum_prod_mul_exp_sum_le hP hf0 hf1 (s := t / 2) (by linarith) (by linarith)
  have hle : ∀ y : Fin n → β, (∏ i, P i (y i)) * (if n * t ≤ ∑ i, f i (y i) then 1 else 0) ≤
      (∏ i, P i (y i)) * exp (t / 2 * ∑ i, f i (y i)) * exp (-(t / 2 * (n * t))) := fun y => by
    rw [mul_assoc, ← exp_add]
    refine mul_le_mul_of_nonneg_left ?_ (hμ0 y)
    split_ifs with h
    · refine one_le_exp ?_
      nlinarith
    · exact (exp_pos _).le
  calc _ ≤ ∑ y : Fin n → β, (∏ i, P i (y i)) * exp (t / 2 * ∑ i, f i (y i)) *
        exp (-(t / 2 * (n * t))) := sum_le_sum fun y _ => hle y
    _ ≤ exp (n * (t / 2) ^ 2) * exp (-(t / 2 * (n * t))) := by
        rw [← sum_mul]
        exact mul_le_mul_of_nonneg_right hm (exp_pos _).le
    _ = _ := by
        rw [← exp_add]
        congr 1
        ring

open Classical in
omit [Fintype α] [Fintype γ] in
/-- **The two-sided Chernoff bound.** `P{|∑ᵢ fᵢ| ≥ n t} ≤ 2 e^{-n t² / 4}`. -/
theorem sum_prod_abs_ge_le (hP : ∀ i, IsPMF (P i)) (hf0 : ∀ i, ∑ b, P i b * f i b = 0)
    (hf1 : ∀ i b, |f i b| ≤ 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∑ y : Fin n → β, (∏ i, P i (y i)) * (if n * t ≤ |∑ i, f i (y i)| then 1 else 0) ≤
      2 * exp (-(n * t ^ 2 / 4)) := by
  have h1 := sum_prod_ge_le hP hf0 hf1 ht0 ht1
  have h2 := sum_prod_ge_le (f := fun i b => -f i b) hP
    (fun i => by simp only [mul_neg, sum_neg_distrib, hf0 i, neg_zero])
    (fun i b => by rw [abs_neg]; exact hf1 i b) ht0 ht1
  have hμ0 : ∀ y : Fin n → β, 0 ≤ ∏ i, P i (y i) := fun y =>
    prod_nonneg fun i _ => (hP i).nonneg _
  have hle : ∀ y : Fin n → β, (∏ i, P i (y i)) * (if n * t ≤ |∑ i, f i (y i)| then 1 else 0) ≤
      (∏ i, P i (y i)) * (if n * t ≤ ∑ i, f i (y i) then 1 else 0) +
      (∏ i, P i (y i)) * (if n * t ≤ ∑ i, -f i (y i) then 1 else 0) := fun y => by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hμ0 y)
    rw [sum_neg_distrib]
    split_ifs with h h3 h4 h4
    all_goals first
      | (exfalso
         rcases le_abs.1 h with h5 | h5
         · exact h3 h5
         · exact h4 h5)
      | norm_num
  calc _ ≤ ∑ y : Fin n → β, ((∏ i, P i (y i)) * (if n * t ≤ ∑ i, f i (y i) then 1 else 0) +
        (∏ i, P i (y i)) * (if n * t ≤ ∑ i, -f i (y i) then 1 else 0)) :=
        sum_le_sum fun y _ => hle y
    _ ≤ _ := by
        rw [sum_add_distrib, two_mul]
        exact add_le_add h1 h2

end Chernoff

/-! ### The conditional typicality lemma with an exponential bound -/

section Conditional

variable {q : α × β → ℝ} {n : ℕ} {x : Fin n → α} {ε ε' : ℝ}

open Classical in
/-- The exponential bound of the conditional typicality lemma. -/
def condExpBound (q : α × β → ℝ) (ε' ε : ℝ) (n : ℕ) : ℝ :=
  ∑ z ∈ univ.filter (fun z => 0 < q z), 2 * exp (-(n * ((ε - ε') * q z) ^ 2 / 4))

/-- **The conditional typicality lemma, exponential form.** Let `ε' < ε ≤ ε' + 1` and
`xⁿ ∈ T_{ε'}^(n)(X)`. If `Yⁿ ∼ ∏ᵢ p(yᵢ|xᵢ)`, then `(xⁿ, Yⁿ)` is not typical with probability at most
a sum of terms `2 e^{-n c_z² / 4}`, with `c_z = (ε - ε') p(z)`. -/
theorem one_sub_condExpBound_le_prob (hq : IsPMF q) (hεε : ε' < ε) (hε1 : ε - ε' ≤ 1)
    (hn : 0 < n) (hx : x ∈ robustTypicalSet (margFst q) n ε') :
    1 - condExpBound q ε' ε n ≤
      prob (channelExt (condPMF q) n x) (condRobustTypicalSet q ε x) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set W := condPMF q
  set μ := channelExt W n x
  have hmarg : ∀ i, 0 < marg q (x i) := fun i => by
    have := pos_of_mem_robustTypicalSet (hq.dist Prod.fst).nonneg hx i
    rw [marg_eq_dist]
    exact this
  have hrow : ∀ i, IsPMF (W (x i)) := fun i => condPMF_isPMF hq.nonneg (hmarg i).ne'
  have hμ : IsPMF μ := ⟨fun y => prod_nonneg fun i _ => (hrow i).nonneg _, by
    rw [show ∑ y, μ y = ∏ i, ∑ b, W (x i) b from (Fintype.prod_sum _).symm]
    simp [(hrow _).sum_eq_one]⟩
  set f : α × β → Fin n → β → ℝ := fun z i c =>
    if x i = z.1 then (if c = z.2 then 1 else 0) - W z.1 z.2 else 0
  set S : α × β → (Fin n → β) → ℝ := fun z y => ∑ i, f z i (y i)
  have hf0 : ∀ z i, ∑ c, W (x i) c * f z i c = 0 := fun z i => by
    simp only [f]
    split_ifs with hi
    · rw [← hi]
      simp [mul_sub, sum_sub_distrib, ← sum_mul, (hrow i).sum_eq_one]
    · simp
  have hf1 : ∀ z i c, |f z i c| ≤ 1 := fun z i c => by
    have h0 := condPMF_nonneg hq.nonneg z.1 z.2
    have h1 := condPMF_le_one hq.nonneg z.1 z.2
    simp only [f]
    rw [abs_le]
    split_ifs <;> constructor <;> linarith
  -- The Chernoff bound for each centered count.
  set c : α × β → ℝ := fun z => (ε - ε') * q z
  set B : α × β → Finset (Fin n → β) := fun z => univ.filter fun y => n * c z ≤ |S z y|
  have hB : ∀ z, 0 < q z → prob μ (B z) ≤ 2 * exp (-(n * c z ^ 2 / 4)) := fun z hz => by
    have hc : 0 < c z := mul_pos (by linarith) hz
    have hc1 : c z ≤ 1 := by
      have := hq.le_one z
      calc c z ≤ 1 * 1 := mul_le_mul hε1 this hz.le zero_le_one
        _ = 1 := one_mul 1
    have h := sum_prod_abs_ge_le hrow (hf0 z) (hf1 z) hc hc1
    refine le_of_eq_of_le ?_ h
    rw [prob, sum_filter]
    refine sum_congr rfl fun y _ => ?_
    simp only [S]
    split_ifs
    · simp only [μ, channelExt, mul_one]
    · simp
  set Pz := univ.filter fun z : α × β => 0 < q z
  have hcover : prob μ (condRobustTypicalSet q ε x)ᶜ ≤ prob μ (Pz.biUnion B) := by
    refine prob_le_prob_of_ae hμ.nonneg fun y hy hy0 => ?_
    rw [mem_compl, mem_condRobustTypicalSet, mem_robustTypicalSet, not_forall] at hy
    obtain ⟨⟨a, b⟩, hab⟩ := hy
    rw [not_le] at hab
    rcases (hq.nonneg (a, b)).lt_or_eq with hpos | hzero
    · refine mem_biUnion.2 ⟨(a, b), by simp [Pz, hpos], ?_⟩
      simp only [B, mem_filter, mem_univ, true_and, S, f, c]
      rw [sum_count_deviation, ← mul_typeOf hn, ← mul_typeOf hn, mul_assoc (n : ℝ) (typeOf x a),
        ← mul_sub, abs_mul, abs_of_pos hn']
      refine mul_le_mul_of_nonneg_left ?_ hn'.le
      have hqW : q (a, b) = marg q a * W a b := (marg_mul_condPMF hq.nonneg a b).symm
      have hxa : |typeOf x a - marg q a| ≤ ε' * marg q a := by
        rw [marg_eq_dist]
        exact mem_robustTypicalSet.1 hx a
      have hW := condPMF_nonneg hq.nonneg a b
      have h2 : |typeOf x a * W a b - q (a, b)| ≤ ε' * q (a, b) := by
        rw [hqW, ← sub_mul, abs_mul, abs_of_nonneg hW, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hxa hW
      have h3 := abs_sub_le (typeOf (zipSeq x y) (a, b)) (typeOf x a * W a b) (q (a, b))
      linarith
    · exfalso
      rw [← hzero, sub_zero, mul_zero, abs_pos] at hab
      have hcount : symbolCount (zipSeq x y) (a, b) ≠ 0 := fun h0 => hab (by simp [typeOf, h0])
      obtain ⟨i, hi⟩ := exists_eq_of_symbolCount_ne_zero hcount
      simp only [zipSeq, Prod.mk.injEq] at hi
      refine hy0 (prod_eq_zero (mem_univ i) ?_)
      rw [hi.1, hi.2]
      simp [W, condPMF, ← hzero]
  have hunion : prob μ (Pz.biUnion B) ≤ condExpBound q ε' ε n := by
    refine (prob_biUnion_le hμ.nonneg _ _).trans ?_
    rw [condExpBound]
    exact sum_le_sum fun z hz => hB z (mem_filter.1 hz).2
  have hc := prob_compl hμ (condRobustTypicalSet q ε x)
  linarith

/-- For every `G > 0`, `e^{nG} condExpBound → 0` if `G` is small compared to `(ε - ε') p(z)`. -/
theorem exists_mul_condExpBound_tendsto (q : α × β → ℝ) {ε ε' : ℝ} (hεε : ε' < ε) :
    ∃ c > 0, ∀ G < c, Tendsto (fun n : ℕ => exp (n * G) * condExpBound q ε' ε n) atTop (𝓝 0) := by
  classical
  set Pz := univ.filter fun z : α × β => 0 < q z
  set v : α × β → ℝ := fun z => ((ε - ε') * q z) ^ 2 / 4
  have hv : ∀ z ∈ Pz, 0 < v z := fun z hz => by
    have h := (mem_filter.1 hz).2
    have : 0 < (ε - ε') * q z := mul_pos (by linarith) h
    positivity
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ z ∈ Pz, c ≤ v z := by
    rcases Pz.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := exists_min_image Pz v hne
      exact ⟨v z₀, hv z₀ hz₀, hmin⟩
  refine ⟨c, hc, fun G hG => ?_⟩
  have e : ∀ n : ℕ, exp (n * G) * condExpBound q ε' ε n =
      ∑ z ∈ Pz, 2 * exp (-(n * (v z - G))) := fun n => by
    rw [condExpBound, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [mul_left_comm, ← exp_add]
    congr 2
    simp only [v]
    ring
  simp only [e]
  have hlim : ∀ z ∈ Pz, Tendsto (fun n : ℕ => 2 * exp (-(n * (v z - G)))) atTop (𝓝 0) :=
    fun z hz => by
      have hpos : 0 < v z - G := by linarith [hcle z hz]
      have h := tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hpos)
      simpa using h.const_mul 2
  simpa using tendsto_finsetSum Pz hlim

end Conditional

/-! ### The Markov lemma -/

section Markov

variable {q : (α × β) × γ → ℝ} {κ : β → γ → ℝ} {n : ℕ} {x : Fin n → α} {y : Fin n → β} {ε ε' : ℝ}

omit [Fintype α] [Fintype β] in
/-- If `q((a, b), c) = p(a, b) κ(c | b)`, the conditional law of `Z` given `(X, Y)` depends on `Y`
only: the Markov chain `X → Y → Z`. -/
lemma channelExt_condPMF_of_markov
    (hq : ∀ a b c, q ((a, b), c) = marg q (a, b) * κ b c)
    (hxy : ∀ i, marg q (x i, y i) ≠ 0) :
    channelExt (condPMF q) n (zipSeq x y) = channelExt κ n y := by
  funext z
  refine prod_congr rfl fun i _ => ?_
  simp only [zipSeq, condPMF]
  rw [hq]
  field_simp [hxy i]

open Classical in
/-- **The Markov lemma (Lecture 13, page 13-6).** Let `X → Y → Z` be a Markov chain with
`p(z | y) = κ(z | y)`, and `(xⁿ, yⁿ) ∈ T_{ε'}^(n)`. Let `φ` be a nonnegative function on the
sequences `zⁿ` with `φ(zⁿ) ≤ e^{-n E'}` on a set `A` on which `κ(zⁿ | yⁿ) ≥ e^{-n E}`. Then the mass
under `φ` of the sequences not typical with `(xⁿ, yⁿ)` is at most
`φ(Aᶜ) + e^{n (E - E')} condExpBound`. -/
theorem sum_not_mem_condRobust_le (hqP : IsPMF q) (hκ : IsChannel κ)
    (hq : ∀ a b c, q ((a, b), c) = marg q (a, b) * κ b c) (hεε : ε' < ε) (hε1 : ε - ε' ≤ 1)
    (hn : 0 < n) (hxy : zipSeq x y ∈ robustTypicalSet (margFst q) n ε')
    {φ : (Fin n → γ) → ℝ} (hφ : ∀ z, 0 ≤ φ z) (A : Finset (Fin n → γ)) {E E' : ℝ}
    (hA : ∀ z ∈ A, exp (-(n * E)) ≤ channelExt κ n y z)
    (hφA : ∀ z ∈ A, φ z ≤ exp (-(n * E'))) :
    ∑ z, (if z ∉ condRobustTypicalSet q ε (zipSeq x y) then φ z else 0) ≤
      ∑ z, (if z ∉ A then φ z else 0) + exp (n * (E - E')) * condExpBound q ε' ε n := by
  have hmarg : ∀ i, marg q (x i, y i) ≠ 0 := fun i => by
    have := pos_of_mem_robustTypicalSet (hqP.dist Prod.fst).nonneg hxy i
    rw [marg_eq_dist]
    exact this.ne'
  have heq := channelExt_condPMF_of_markov (x := x) (y := y) hq hmarg
  have hμ : IsPMF (channelExt κ n y) := hκ.ext n y
  have hb := one_sub_condExpBound_le_prob hqP hεε hε1 hn hxy
  rw [heq] at hb
  set T := condRobustTypicalSet q ε (zipSeq x y)
  have hoff : ∑ z, (if z ∉ T then channelExt κ n y z else 0) ≤ condExpBound q ε' ε n := by
    have h1 : ∑ z, (if z ∉ T then channelExt κ n y z else 0) =
        1 - prob (channelExt κ n y) T := by
      rw [eq_sub_iff_add_eq, ← hμ.sum_eq_one]
      have e : prob (channelExt κ n y) T =
          ∑ z, if z ∈ T then channelExt κ n y z else 0 := by
        rw [prob, sum_ite_mem, univ_inter]
      rw [e, ← sum_add_distrib]
      refine sum_congr rfl fun z _ => ?_
      split_ifs <;> simp
    linarith
  have hexp : 0 < exp (n * (E - E')) := exp_pos _
  have hpt : ∀ z, (if z ∉ T then φ z else 0) ≤ (if z ∉ A then φ z else 0) +
      exp (n * (E - E')) * (if z ∉ T then channelExt κ n y z else 0) := fun z => by
    by_cases hT : z ∈ T
    · simp only [hT, not_true_eq_false, ite_false, mul_zero, add_zero]
      split_ifs
      all_goals first | exact hφ z | exact le_rfl
    · by_cases hAz : z ∈ A
      · simp only [hT, hAz, not_true_eq_false, not_false_eq_true, ite_true, ite_false, zero_add]
        have h1 := hφA z hAz
        have h2 := hA z hAz
        calc φ z ≤ exp (-(n * E')) := h1
          _ = exp (n * (E - E')) * exp (-(n * E)) := by
              rw [← exp_add]
              congr 1
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 hexp.le
      · simp only [hT, hAz, not_false_eq_true, ite_true]
        have := channelExt_nonneg hκ y z
        nlinarith [mul_nonneg hexp.le this]
  calc _ ≤ ∑ z, ((if z ∉ A then φ z else 0) +
        exp (n * (E - E')) * (if z ∉ T then channelExt κ n y z else 0)) :=
        sum_le_sum fun z _ => hpt z
    _ = ∑ z, (if z ∉ A then φ z else 0) +
        exp (n * (E - E')) * ∑ z, (if z ∉ T then channelExt κ n y z else 0) := by
        rw [sum_add_distrib, mul_sum]
    _ ≤ _ := by
        gcongr

end Markov

end InfoTheory
