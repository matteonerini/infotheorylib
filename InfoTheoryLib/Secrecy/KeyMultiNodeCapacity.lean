/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyMultiNodeBinning

/-!
# Secret key agreement with many nodes: the capacity

Theorem 9 of Lecture 23 of El Gamal and Kim: when all the nodes know `Z`, the secret key capacity is
`H(X^N | Z) - R_CFO([1 : N] | Z)`, in bits.

## Main statements

* `colNode_le`, `colKey_le`: the collisions, for the rates of the proof.
* `eventually_multiBin`: the key from random binning, on an i.i.d. sequence.
* `isAchievableMultiKey_of_lt`: the achievability.
* `multiKeyCapacity_eq`: **Theorem 9 of Lecture 23**.
* `zRegion_eq_mwRegion`, `rCFOZ_eq_rCFO`: the region and the rate are those of Lecture 21 for the
  sources `(Xⱼ, Z)`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {N n : ℕ} {α : Fin N → Type*} [∀ j, Fintype (α j)] {γ : Type*} [Fintype γ]
  {p : mLetter α γ → ℝ}

/-- The product of the sizes of the bins on `S`. -/
lemma prod_one_div_two_pow_le (n : ℕ) (Rb : Fin N → ℝ) (S : Finset (Fin N)) :
    ∏ j ∈ S, (1 / ((2 ^ ⌈n * Rb j⌉₊ : ℕ) : ℝ)) ≤ exp (-(n * ((∑ j ∈ S, Rb j) * log 2))) := by
  have h : ∀ j ∈ S, 1 / ((2 ^ ⌈n * Rb j⌉₊ : ℕ) : ℝ) ≤ exp (-(n * (Rb j * log 2))) := fun j _ => by
    rw [exp_neg, one_div]
    refine inv_anti₀ (exp_pos _) ?_
    have h₁ := le_log_two_pow_ceil n (Rb j)
    have hpos : (0 : ℝ) < ((2 ^ ⌈n * Rb j⌉₊ : ℕ) : ℝ) := by positivity
    rw [← exp_log hpos]
    exact exp_le_exp.2 h₁
  refine (prod_le_prod₀ (fun _ _ => by positivity) h).trans (le_of_eq ?_)
  rw [← exp_sum]
  congr 1
  rw [sum_mul, mul_sum, sum_neg_distrib]

/-- The collisions of the decoder of the node `k`. -/
lemma colNode_le {Rb : Fin N → ℝ} {t g : ℝ}
    (hS : ∀ S : Finset (Fin N), S.Nonempty → S ≠ univ →
      zCondH p S + t * zCondH p S + g ≤ (∑ j ∈ S, Rb j) * log 2) (k : Fin N) :
    colNode p (fun j => 2 ^ ⌈n * Rb j⌉₊) n t k ≤ 2 ^ N * exp (-(n * g)) := by
  classical
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hterm : ∀ S ∈ univ.filter fun S : Finset (Fin N) => S.Nonempty ∧ k ∉ S,
      exp (n * (zCondH p S + t * zCondH p S)) * ∏ j ∈ S, (1 / ((2 ^ ⌈n * Rb j⌉₊ : ℕ) : ℝ)) ≤
        exp (-(n * g)) := fun S hS' => by
    obtain ⟨hne, hk⟩ := (mem_filter.1 hS').2
    have hSu : S ≠ univ := fun h => hk (h ▸ mem_univ k)
    refine (mul_le_mul_of_nonneg_left (prod_one_div_two_pow_le n Rb S) (exp_pos _).le).trans ?_
    rw [← exp_add]
    refine exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (hS S hne hSu) hn0
    have e : (n : ℝ) * (zCondH p S + t * zCondH p S + g) =
        n * (zCondH p S + t * zCondH p S) + n * g := by ring
    linarith
  have hcard : ((univ.filter fun S : Finset (Fin N) => S.Nonempty ∧ k ∉ S).card : ℝ) ≤ 2 ^ N := by
    have := card_filter_le (univ : Finset (Finset (Fin N))) fun S => S.Nonempty ∧ k ∉ S
    rw [card_univ, Fintype.card_finset, Fintype.card_fin] at this
    exact_mod_cast this
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard (exp_pos _).le

/-- The collisions of the decoder with the key. -/
lemma colKey_le {Rb : Fin N → ℝ} {t g R : ℝ}
    (hS : ∀ S : Finset (Fin N), S.Nonempty → S ≠ univ →
      zCondH p S + t * zCondH p S + g ≤ (∑ j ∈ S, Rb j) * log 2)
    (hU : zCondH p univ + t * zCondH p univ + g ≤ (∑ j, Rb j) * log 2 + R * log 2) :
    colKey p (fun j => 2 ^ ⌈n * Rb j⌉₊) (2 ^ ⌈n * R⌉₊) n t ≤ 2 ^ N * exp (-(n * g)) := by
  classical
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hK : 1 / ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ exp (-(n * (R * log 2))) := by
    rw [exp_neg, one_div]
    refine inv_anti₀ (exp_pos _) ?_
    have h₁ := le_log_two_pow_ceil n R
    have hpos : (0 : ℝ) < ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := by positivity
    rw [← exp_log hpos]
    exact exp_le_exp.2 h₁
  have hK1 : 1 / ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.one_le_two_pow
  have hterm : ∀ S ∈ univ.filter fun S : Finset (Fin N) => S.Nonempty,
      exp (n * (zCondH p S + t * zCondH p S)) * (∏ j ∈ S, (1 / ((2 ^ ⌈n * Rb j⌉₊ : ℕ) : ℝ))) *
        (1 / ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ)) ≤ exp (-(n * g)) := fun S hS' => by
    have hne := (mem_filter.1 hS').2
    have hP := prod_one_div_two_pow_le n Rb S
    have hP0 : (0 : ℝ) ≤ ∏ j ∈ S, (1 / ((2 ^ ⌈n * Rb j⌉₊ : ℕ) : ℝ)) :=
      prod_nonneg fun _ _ => by positivity
    by_cases hSu : S = univ
    · subst hSu
      calc _ ≤ exp (n * (zCondH p univ + t * zCondH p univ)) *
            exp (-(n * ((∑ j, Rb j) * log 2))) * exp (-(n * (R * log 2))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hP (exp_pos _).le) hK (by positivity)
              (by positivity)
        _ = exp (n * (zCondH p univ + t * zCondH p univ) + -(n * ((∑ j, Rb j) * log 2)) +
            -(n * (R * log 2))) := by rw [exp_add, exp_add]
        _ ≤ _ := by
            refine exp_le_exp.2 ?_
            have := mul_le_mul_of_nonneg_left hU hn0
            have e₁ : (n : ℝ) * (zCondH p univ + t * zCondH p univ + g) =
                n * (zCondH p univ + t * zCondH p univ) + n * g := by ring
            have e₂ : (n : ℝ) * ((∑ j, Rb j) * log 2 + R * log 2) =
                n * ((∑ j, Rb j) * log 2) + n * (R * log 2) := by ring
            linarith
    · calc _ ≤ exp (n * (zCondH p S + t * zCondH p S)) *
            exp (-(n * ((∑ j ∈ S, Rb j) * log 2))) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hP (exp_pos _).le) hK1 (by positivity)
              (by positivity)
        _ = exp (n * (zCondH p S + t * zCondH p S) + -(n * ((∑ j ∈ S, Rb j) * log 2))) := by
            rw [mul_one, exp_add]
        _ ≤ _ := by
            refine exp_le_exp.2 ?_
            have := mul_le_mul_of_nonneg_left (hS S hne hSu) hn0
            have e : (n : ℝ) * (zCondH p S + t * zCondH p S + g) =
                n * (zCondH p S + t * zCondH p S) + n * g := by ring
            linarith
  have hcard : ((univ.filter fun S : Finset (Fin N) => S.Nonempty).card : ℝ) ≤ 2 ^ N := by
    have := card_filter_le (univ : Finset (Finset (Fin N))) fun S => S.Nonempty
    rw [card_univ, Fintype.card_finset, Fintype.card_fin] at this
    exact_mod_cast this
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard (exp_pos _).le

/-- `H(X^N | Z)` in the form of `zCondH`. -/
lemma zCondH_univ (hp : IsPMF p) : zCondH p univ = H[Prod.fst | Prod.snd ; p] := by
  classical
  obtain ⟨a₀⟩ : Nonempty (mLetter α γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  rw [zCondH]
  have e₁ : H[(fun a : mLetter α γ => maskL univ a.1) | (fun a => (maskL univᶜ a.1, a.2)) ; p] =
      H[Prod.fst | (fun a : mLetter α γ => (maskL univᶜ a.1, a.2)) ; p] :=
    condEntropy_eq_of_mutual hp _ (maskL univ) (fun v j => (v j).getD (a₀.1 j)) rfl (by
      funext a
      funext j
      simp [maskL])
  rw [e₁]
  refine condEntropy_eq_of_comp hp _ (fun w => w.2) (fun z => (fun _ => none, z)) rfl ?_
  funext a
  refine Prod.ext (funext fun j => ?_) rfl
  simp [maskL]

/-- `H(∅ | ...)`: the conditional entropy on the empty set is `0`, and it is nonnegative. -/
lemma zCondH_nonneg (hp : IsPMF p) (S : Finset (Fin N)) : 0 ≤ zCondH p S :=
  condEntropy_nonneg hp _ _

/-- The region is not empty. -/
lemma zRegion_nonempty (hp : IsPMF p) : (zRegion p).Nonempty := by
  classical
  have hl := log_pos one_lt_two
  set C := ∑ S : Finset (Fin N), zCondH p S / log 2 with hC
  have hC0 : 0 ≤ C := sum_nonneg fun S _ => div_nonneg (zCondH_nonneg hp S) hl.le
  refine ⟨fun _ => C, fun _ => hC0, fun S _ => ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · have h₀ : zCondH p ∅ = 0 :=
      (condEntropy_eq_zero_iff hp _ _).2 ⟨fun _ _ => none, fun a _ => maskL_empty a.1⟩
    simp [h₀]
  · have h₁ : zCondH p S / log 2 ≤ C :=
      single_le_sum (f := fun S => zCondH p S / log 2)
        (fun S _ => div_nonneg (zCondH_nonneg hp S) hl.le) (mem_univ S)
    rw [sum_const, nsmul_eq_mul]
    have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast hne.card_pos
    nlinarith

/-- The arithmetic of the end of the proof of achievability. -/
lemma multiBin_arith {nR A H₀ δ₂ η L l₂ c₀ ε logM logK HM HK e₁ I₀ Hk : ℝ} (hn : 0 < nR)
    (hδ : 8 * δ₂ ≤ ε) (hηL : η * L ≤ ε / 8) (hc : c₀ * l₂ ≤ nR * (ε / 4)) (hl : 0 ≤ l₂)
    (hε : 0 < ε) (hA : logK ≤ nR * A + l₂)
    (hM : logM ≤ nR * (H₀ - A + δ₂) + (c₀ - 2) * l₂) (hHM : HM ≤ logM) (hHK : HK ≤ logK)
    (he₁ : e₁ ≤ l₂ + nR * (η * L))
    (hI : I₀ ≤ HK + HM - nR * H₀ + e₁) (hH : nR * H₀ - HM - e₁ ≤ HK) (hHk : HK = Hk) :
    I₀ ≤ nR * ε ∧ nR * (A - ε) ≤ Hk := by
  have h₁ : nR * (η * L) ≤ nR * (ε / 8) := mul_le_mul_of_nonneg_left hηL hn.le
  have h₂ : nR * δ₂ ≤ nR * (ε / 8) := mul_le_mul_of_nonneg_left (by linarith) hn.le
  have e₃ : nR * (H₀ - A + δ₂) = nR * H₀ - nR * A + nR * δ₂ := by ring
  have e₄ : (c₀ - 2) * l₂ = c₀ * l₂ - 2 * l₂ := by ring
  have e₅ : nR * (A - ε) = nR * A - nR * ε := by ring
  have e₆ : nR * ε = nR * (ε / 8) + nR * (ε / 8) + nR * (ε / 4) + nR * (ε / 2) := by ring
  have h₃ : 0 ≤ nR * (ε / 2) := by positivity
  rw [← hHk]
  constructor <;> linarith

/-- The rates of the proof. -/
lemma exists_multiBin_rates (hp : IsPMF p) (hN : 0 < N) {R δ₂ : ℝ}
    (hlt : R < zCondH p univ / log 2 - rCFOZ p) (hδ₂ : 0 < δ₂) :
    ∃ (Rb : Fin N → ℝ) (t g : ℝ), (∀ j, 0 ≤ Rb j) ∧ 0 < t ∧ 0 < g ∧
      (∀ S : Finset (Fin N), S.Nonempty → S ≠ univ →
        zCondH p S + t * zCondH p S + g ≤ (∑ j ∈ S, Rb j) * log 2) ∧
      zCondH p univ + t * zCondH p univ + g ≤ (∑ j, Rb j) * log 2 + R * log 2 ∧
      (∑ j, Rb j) * log 2 = zCondH p univ - R * log 2 + δ₂ := by
  classical
  have hl := log_pos one_lt_two
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnonempty : ((fun R : Fin N → ℝ => ∑ j, R j) '' zRegion p).Nonempty :=
    (zRegion_nonempty hp).image _
  have hlt' : rCFOZ p < zCondH p univ / log 2 - R := by linarith
  obtain ⟨_, ⟨R', hR', rfl⟩, hlt₂⟩ := exists_lt_of_csInf_lt hnonempty hlt'
  set c := zCondH p univ - R * log 2 - (∑ j, R' j) * log 2 with hc
  have hc0 : 0 < c := by
    have h₁ := (lt_div_iff₀ hl).1 (show (∑ j, R' j) + R < zCondH p univ / log 2 by linarith)
    rw [add_mul] at h₁
    linarith
  set g₀ := (c + δ₂) / N with hg₀
  have hg₀0 : 0 < g₀ := by positivity
  set Rb : Fin N → ℝ := fun j => R' j + g₀ / log 2 with hRb
  have hsumS : ∀ S : Finset (Fin N), (∑ j ∈ S, Rb j) * log 2 =
      (∑ j ∈ S, R' j) * log 2 + S.card * g₀ := fun S => by
    simp only [hRb, sum_add_distrib, sum_const, nsmul_eq_mul]
    field_simp
  set m := min g₀ δ₂ with hm
  have hm0 : 0 < m := lt_min hg₀0 hδ₂
  set Z₀ := ∑ S : Finset (Fin N), zCondH p S with hZ₀
  have hZ₀0 : 0 ≤ Z₀ := sum_nonneg fun S _ => zCondH_nonneg hp S
  set t := m / (2 * (Z₀ + 1)) with ht
  have ht0 : 0 < t := by positivity
  have hz : ∀ S, t * zCondH p S ≤ m / 2 := fun S => by
    have h₁ : zCondH p S ≤ Z₀ :=
      single_le_sum (f := fun S => zCondH p S) (fun S _ => zCondH_nonneg hp S) (mem_univ S)
    have h₂ : t * zCondH p S ≤ t * (Z₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) ht0.le
    have h₃ : t * (Z₀ + 1) = m / 2 := by
      rw [ht]
      field_simp
    linarith
  refine ⟨Rb, t, m / 2, fun j => add_nonneg (hR'.1 j) (by positivity), ht0, by positivity,
    fun S hne hSu => ?_, ?_, ?_⟩
  · have h₁ := (div_le_iff₀ hl).1 (hR'.2 S hSu)
    have h₂ := hz S
    have h₃ : (1 : ℝ) ≤ S.card := by exact_mod_cast hne.card_pos
    have h₄ : m ≤ g₀ := min_le_left _ _
    have h₅ : g₀ ≤ S.card * g₀ := by nlinarith
    rw [hsumS]
    linarith
  · have h₁ := hsumS univ
    rw [card_univ, Fintype.card_fin] at h₁
    have h₂ : (N : ℝ) * g₀ = c + δ₂ := by
      rw [hg₀]
      field_simp
    have h₃ := hz univ
    have h₄ : m ≤ δ₂ := min_le_right _ _
    rw [h₁, h₂]
    linarith
  · have h₁ := hsumS univ
    rw [card_univ, Fintype.card_fin] at h₁
    have h₂ : (N : ℝ) * g₀ = c + δ₂ := by
      rw [hg₀]
      field_simp
    rw [h₁, h₂]
    ring

open Classical in
/-- **Pages 23-54 to 23-56 of [elgamal2010]: the key from random binning, on an i.i.d. sequence.**
If `R < H(X^N | Z) - R_CFO`, in bits, then for every `ε` and all large `n` there are bins, a key and
decoders, such that the probability of error of the nodes is at most `ε`, with `I(K; Zⁿ, M) ≤ n ε`
and `H(K) ≥ n (R - ε)`. -/
theorem eventually_multiBin (hp : IsPMF p) (hN : 0 < N) {R : ℝ} (hR : 0 ≤ R)
    (hlt : R < zCondH p univ / log 2 - rCFOZ p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ (M : Fin N → ℕ) (_ : ∀ j, NeZero (M j))
      (B : ∀ j, Fin (seqN α n j) → Fin (M j))
      (C : Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin (2 ^ ⌈n * R⌉₊))
      (D : ∀ k, (Fin n → α k) → (Fin n → γ) → (∀ j, Fin (M j)) → Fin n → ∀ j, α j),
      (∑ ω : Fin n → mLetter α γ, iidPMF p n ω *
        (∑ k, if D k (fun i => (ω i).1 k) (fun i => (ω i).2)
          (manyBin B fun i => (ω i).1) ≠ (fun i => (ω i).1) then 1 else 0)) ≤ ε ∧
      I[(fun ω : Fin n → mLetter α γ => C (Fintype.equivFin _ fun i => (ω i).1)) :
        pair (fun ω i => (ω i).2) (fun ω => manyBin B fun i => (ω i).1) ; iidPMF p n] ≤ n * ε ∧
      n * (R * log 2 - ε) ≤
        H[(fun ω : Fin n → mLetter α γ => C (Fintype.equivFin _ fun i => (ω i).1)) ; iidPMF p n] :=
          by
  have hl := log_pos one_lt_two
  set H₀ := zCondH p univ with hH₀
  set A := R * log 2 with hA
  set δ₂ := ε / 8 with hδ₂
  have hδ₂0 : 0 < δ₂ := by positivity
  obtain ⟨Rb, t, g, hRb0, ht0, hg0, hS, hU, hsum⟩ := exists_multiBin_rates hp hN hlt hδ₂0
  set L := log (Fintype.card (∀ j, α j)) with hL
  have hL0 : 0 ≤ L := log_natCast_nonneg _
  set η := min ε (ε / (8 * (L + 1))) with hη
  have hη0 : 0 < η := lt_min hε (by positivity)
  have hη₁ : η ≤ ε := min_le_left _ _
  have hη₂ : η * L ≤ ε / 8 := by
    have h₁ : η ≤ ε / (8 * (L + 1)) := min_le_right _ _
    have h₂ : η * (8 * (L + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 h₁
    nlinarith
  set Bd : ℕ → ℝ := fun n => (N + 1) * (1 - prob (iidPMF p n) (robustTypicalSet p n t)) +
    (N + 1) * (2 ^ N * exp (-(n * g))) with hBd
  have hBdlim : Tendsto Bd atTop (𝓝 0) := by
    have t₁ : Tendsto (fun n => 1 - prob (iidPMF p n) (robustTypicalSet p n t)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet hp ht0).const_sub 1
    have t₂ := tendsto_exp_neg_mul_nat hg0
    simpa [hBd] using (t₁.const_mul ((N : ℝ) + 1)).add ((t₂.const_mul ((2 : ℝ) ^ N)).const_mul
      ((N : ℝ) + 1))
  filter_upwards [(tendsto_order.1 hBdlim).2 _ hη0,
    eventually_gt_atTop ⌈4 * ((N + 2) * log 2) / ε⌉₊] with n hn hn1
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hnc : ((N : ℝ) + 2) * log 2 ≤ n * (ε / 4) := by
    have h₁ : 4 * ((N + 2) * log 2) / ε < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
    rw [div_lt_iff₀ hε] at h₁
    linarith
  have hMne : ∀ j, NeZero ((fun j => 2 ^ ⌈n * Rb j⌉₊) j) := fun j => ⟨by positivity⟩
  have hKne : NeZero (2 ^ ⌈n * R⌉₊) := ⟨by positivity⟩
  obtain ⟨B, C, d, hbin⟩ := exists_multiBin (n := n) (M := fun j => 2 ^ ⌈n * Rb j⌉₊)
    (Kb := 2 ^ ⌈n * R⌉₊) (γ := γ) hp t
  have hμ := iidPMF_isPMF hp n
  -- The errors.
  set Ind : (Fin n → mLetter α γ) → ℝ := fun ω => ∑ k,
    if decNode (robustTypicalSet p n t) B d k (fun i => (ω i).1 k) (fun i => (ω i).2)
      (manyBin B fun i => (ω i).1) ≠ (fun i => (ω i).1) then 1 else 0 with hInd
  set IndK : (Fin n → mLetter α γ) → ℝ := fun ω =>
    if decKey (robustTypicalSet p n t) B C d (fun i => (ω i).2) (manyBin B fun i => (ω i).1)
      (C (Fintype.equivFin _ fun i => (ω i).1)) ≠ (fun i => (ω i).1) then 1 else 0 with hIndK
  have hI0 : ∀ ω, 0 ≤ Ind ω := fun ω => sum_nonneg fun k _ => by split_ifs <;> norm_num
  have hK0 : ∀ ω, 0 ≤ IndK ω := fun ω => by simp only [hIndK]; split_ifs <;> norm_num
  have hcolN : ∑ k, colNode p (fun j => 2 ^ ⌈n * Rb j⌉₊) n t k ≤ N * (2 ^ N * exp (-(n * g))) := by
    refine (sum_le_sum fun k _ => colNode_le hS k).trans (le_of_eq ?_)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcolK := colKey_le (n := n) (R := R) hS hU
  have htot : ∑ ω, iidPMF p n ω * (Ind ω + IndK ω) ≤ η := by
    refine hbin.trans (le_trans ?_ hn.le)
    simp only [hBd]
    linarith
  have hsplit : ∑ ω, iidPMF p n ω * (Ind ω + IndK ω) =
      ∑ ω, iidPMF p n ω * Ind ω + ∑ ω, iidPMF p n ω * IndK ω := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by ring
  have hs₁ : 0 ≤ ∑ ω, iidPMF p n ω * Ind ω :=
    sum_nonneg fun ω _ => mul_nonneg (hμ.nonneg ω) (hI0 ω)
  have hs₂ : 0 ≤ ∑ ω, iidPMF p n ω * IndK ω :=
    sum_nonneg fun ω _ => mul_nonneg (hμ.nonneg ω) (hK0 ω)
  -- The entropies.
  set T : (Fin n → mLetter α γ) → Fin n → ∀ j, α j := fun ω i => (ω i).1 with hT
  set O : (Fin n → mLetter α γ) → Fin n → γ := fun ω i => (ω i).2 with hO
  set fM : (Fin n → ∀ j, α j) → ∀ j, Fin (2 ^ ⌈n * Rb j⌉₊) := manyBin B with hfM
  set fK : (Fin n → ∀ j, α j) → Fin (2 ^ ⌈n * R⌉₊) := fun x => C (Fintype.equivFin _ x) with hfK
  have hF := fano_weak hμ T (pair (pair (fM ∘ T) (fK ∘ T)) O) (fun w => decKey
    (robustTypicalSet p n t) B C d w.2 w.1.1 w.1.2)
  have hcard : log (Fintype.card (Fin n → ∀ j, α j)) = n * L := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  rw [hcard] at hF
  have herr : InfoTheory.errProb (iidPMF p n) T (pair (pair (fM ∘ T) (fK ∘ T)) O) (fun w => decKey
      (robustTypicalSet p n t) B C d w.2 w.1.1 w.1.2) = ∑ ω, iidPMF p n ω * IndK ω := by
    simp only [InfoTheory.errProb, hIndK]
    refine sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp_all [pair]
  rw [herr] at hF
  have hPK : ∑ ω, iidPMF p n ω * IndK ω ≤ η := by linarith
  have he₁ : H[T | pair (pair (fM ∘ T) (fK ∘ T)) O ; iidPMF p n] ≤ log 2 + n * (η * L) := by
    have h₁ : (∑ ω, iidPMF p n ω * IndK ω) * (n * L) ≤ η * (n * L) :=
      mul_le_mul_of_nonneg_right hPK (by positivity)
    have e : η * ((n : ℝ) * L) = n * (η * L) := by ring
    linarith
  have hHTO : H[T | O ; iidPMF p n] = n * H₀ := by
    rw [condEntropy_iid_comp hp n Prod.fst Prod.snd, hH₀, zCondH_univ hp]
  have hHM : H[fM ∘ T ; iidPMF p n] ≤ log (Fintype.card (∀ j, Fin (2 ^ ⌈n * Rb j⌉₊))) :=
    entropyRV_le_log_card hμ _
  have hHK : H[fK ∘ T ; iidPMF p n] ≤ log (Fintype.card (Fin (2 ^ ⌈n * R⌉₊))) :=
    entropyRV_le_log_card hμ _
  have hlogK : log (Fintype.card (Fin (2 ^ ⌈n * R⌉₊))) ≤ n * A + log 2 := by
    rw [Fintype.card_fin]
    exact log_two_pow_ceil_le n hR
  have hlogM : log (Fintype.card (∀ j, Fin (2 ^ ⌈n * Rb j⌉₊))) ≤
      n * (H₀ - A + δ₂) + ((N + 2) - 2) * log 2 := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    push_cast
    rw [log_prod fun j _ => by positivity]
    have h₁ : ∀ j ∈ (univ : Finset (Fin N)), log ((2 : ℝ) ^ ⌈n * Rb j⌉₊) ≤
        n * (Rb j * log 2) + log 2 := fun j _ => by
      have := log_two_pow_ceil_le n (hRb0 j)
      push_cast at this
      exact this
    refine (sum_le_sum h₁).trans (le_of_eq ?_)
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum, ← sum_mul,
      hsum]
    ring
  have hkey := entropy_key_ge_of_decodable hμ T O fM fK
  have hleak := mutualInfo_key_le_of_decodable hμ T O fM fK
  rw [hHTO] at hkey hleak
  obtain ⟨hfin₁, hfin₂⟩ := multiBin_arith (nR := (n : ℝ)) (A := A) (H₀ := H₀) (δ₂ := δ₂) (η := η)
    (L := L) (l₂ := log 2) (c₀ := (N : ℝ) + 2) (ε := ε) hn0 (by rw [hδ₂]; linarith) hη₂ hnc hl.le hε
    hlogK hlogM hHM hHK he₁ hleak hkey rfl
  refine ⟨fun j => 2 ^ ⌈n * Rb j⌉₊, hMne, B, C, decNode (robustTypicalSet p n t) B d, ?_, hfin₁,
    hfin₂⟩
  have : ∑ ω, iidPMF p n ω * Ind ω ≤ η := by linarith
  exact this.trans hη₁

/-! ### The code -/

section Code

variable {M : Fin N → ℕ} [∀ j, NeZero (M j)] {Kb : ℕ}

/-- **Pages 23-54 and 23-55 of [elgamal2010].** The code: the node `j` sends the bin of `Xⱼⁿ`. Each
node decodes all the sequences and takes the key of them. The private random variables are
trivial. -/
def multiCode (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (C : Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb)
    (D : ∀ k, (Fin n → α k) → (Fin n → γ) → (∀ j, Fin (M j)) → Fin n → ∀ j, α j) :
    MultiKeyCode (spk := id) M Kb (mObs α γ (fun _ => Unit) n) where
  enc l a _ := B l (Fintype.equivFin (Fin n → α l) a.1)
  key k a h := C (Fintype.equivFin _ (D k a.1 a.2.1 h))

omit [Fintype γ] in
/-- The transcript of the code. -/
lemma transB_multiCode (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (C : Fin (Fintype.card (Fin n → ∀ j, α j)) → Fin Kb)
    (D : ∀ k, (Fin n → α k) → (Fin n → γ) → (∀ j, Fin (M j)) → Fin n → ∀ j, α j)
    (w : mBlock α γ (fun _ => Unit) n) :
    (multiCode B C D).transB w = manyBin B fun i => (w.1 i).1 := by
  funext l
  simp only [MultiKeyCode.transB]
  rw [run_apply]
  rfl

/-- The trivial private random variables. -/
abbrev unitLaw (N : ℕ) : ∀ _ : Fin N, Unit → ℝ := fun _ _ => 1

lemma unitLaw_isPMF (j : Fin N) : IsPMF (unitLaw N j) := ⟨fun _ => zero_le_one, by simp⟩

/-- The law of the block is the law of the sequence, for trivial private random variables. -/
lemma dist_fst_block (n : ℕ) :
    dist (secBlockLaw p (seedsLaw (unitLaw N)) n) Prod.fst = iidPMF p n := by
  rw [secBlockLaw]
  exact dist_prodDist_fst (seedsLaw_isPMF unitLaw_isPMF) _

end Code

/-- The final arithmetic for the keys of the nodes. -/
theorem isAchievableMultiKey_of_lt (hp : IsPMF p) (hN : 0 < N) {R : ℝ} (hR : 0 ≤ R)
    (hlt : R < zCondH p univ / log 2 - rCFOZ p) : IsAchievableMultiKey p R := by
  classical
  have hl := log_pos one_lt_two
  have hA : 0 ≤ R * log 2 := mul_nonneg hR hl.le
  refine ⟨hR, fun ε hε => ?_⟩
  set ε₀ := min 1 (ε / (2 * (R * log 2 + 2))) with hε₀
  have hε₀0 : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₁ : ε₀ ≤ 1 := min_le_left _ _
  have hε₂ : ε₀ * (R * log 2 + 2) ≤ ε / 2 := by
    have h₁ : ε₀ ≤ ε / (2 * (R * log 2 + 2)) := min_le_right _ _
    have h₂ := (le_div_iff₀ (by positivity)).1 h₁
    linarith
  have hsmall : ε₀ ≤ ε / 2 := by
    have : ε₀ * 1 ≤ ε₀ * (R * log 2 + 2) := mul_le_mul_of_nonneg_left (by linarith) hε₀0.le
    linarith
  filter_upwards [eventually_multiBin hp hN hR hlt hε₀0,
    eventually_gt_atTop ⌈8 * log 2 / ε⌉₊] with n hn hn1
  obtain ⟨M, hM, B, C, D, herr, hleak, hkey⟩ := hn
  have hnε : 4 * log 2 ≤ n * (ε / 2) := by
    have h₁ : 8 * log 2 / ε < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
    rw [div_lt_iff₀ hε] at h₁
    linarith
  set c := multiCode (Kb := 2 ^ ⌈n * R⌉₊) B C D with hc
  have hμ : IsPMF (secBlockLaw p (seedsLaw (unitLaw N)) n) :=
    secBlockLaw_isPMF hp (seedsLaw_isPMF unitLaw_isPMF) n
  have hμ₀ := iidPMF_isPMF hp n
  have hd := dist_fst_block (N := N) (p := p) (α := α) (γ := γ) n
  set K₀ : (Fin n → mLetter α γ) → Fin (2 ^ ⌈n * R⌉₊) :=
    fun ω => C (Fintype.equivFin _ fun i => (ω i).1) with hK₀
  set V : (Fin n → mLetter α γ) → (Fin n → γ) × ∀ j, Fin (M j) :=
    pair (fun ω i => (ω i).2) (fun ω => manyBin B fun i => (ω i).1) with hV
  have hVB : pair eveM c.transB = V ∘ (Prod.fst : mBlock α γ (fun _ => Unit) n → _) := by
    funext w
    exact Prod.ext rfl (transB_multiCode B C D w)
  have hKB : ∀ k, c.keyB k = (fun ω => C (Fintype.equivFin _ (D k (fun i => (ω i).1 k)
      (fun i => (ω i).2) (manyBin B fun i => (ω i).1)))) ∘
      (Prod.fst : mBlock α γ (fun _ => Unit) n → _) := fun k => by
    funext w
    simp only [MultiKeyCode.keyB, Function.comp]
    rw [hc, transB_multiCode]
    rfl
  set K₀B := K₀ ∘ (Prod.fst : mBlock α γ (fun _ => Unit) n → _) with hK₀B
  -- The error of one node.
  set Ind : (Fin n → mLetter α γ) → Fin N → ℝ := fun ω k =>
    if D k (fun i => (ω i).1 k) (fun i => (ω i).2) (manyBin B fun i => (ω i).1) ≠
      (fun i => (ω i).1) then 1 else 0 with hInd
  have hInd0 : ∀ ω k, 0 ≤ Ind ω k := fun ω k => by simp only [hInd]; split_ifs <;> norm_num
  have hone : ∀ k, InfoTheory.errProb (secBlockLaw p (seedsLaw (unitLaw N)) n) K₀B (c.keyB k) id ≤
      ε₀ := fun k => by
    refine le_trans ?_ herr
    have h₁ := errProb_image (secBlockLaw p (seedsLaw (unitLaw N)) n)
      (Prod.fst : mBlock α γ (fun _ => Unit) n → _) K₀ (fun ω => C (Fintype.equivFin _
        (D k (fun i => (ω i).1 k) (fun i => (ω i).2) (manyBin B fun i => (ω i).1))))
    rw [hd] at h₁
    rw [hKB k, ← h₁]
    simp only [InfoTheory.errProb, id]
    refine sum_le_sum fun ω _ => ?_
    have h₀ := hμ₀.nonneg ω
    have hle : Ind ω k ≤ ∑ k', Ind ω k' :=
      single_le_sum (f := fun k' => Ind ω k') (fun k' _ => hInd0 ω k') (mem_univ k)
    by_cases he : D k (fun i => (ω i).1 k) (fun i => (ω i).2) (manyBin B fun i => (ω i).1) =
        (fun i => (ω i).1)
    · simp only [he, ne_eq, not_true_eq_false, ite_false, hK₀]
      exact mul_nonneg h₀ (sum_nonneg fun k' _ => hInd0 ω k')
    · have h₂ : Ind ω k = 1 := by simp [hInd, he]
      rw [h₂] at hle
      have h₃ := mul_le_mul_of_nonneg_left hle h₀
      rw [mul_one] at h₃
      split_ifs
      · exact h₃
      · exact mul_nonneg h₀ (sum_nonneg fun k' _ => hInd0 ω k')
  have hI₀ : I[K₀B : pair eveM c.transB ; secBlockLaw p (seedsLaw (unitLaw N)) n] ≤ n * ε₀ := by
    rw [hVB, mutualInfo_comp, hd]
    exact hleak
  have hH₀ : n * (R * log 2 - ε₀) ≤ H[K₀B ; secBlockLaw p (seedsLaw (unitLaw N)) n] := by
    have h₂ := entropyRV_comp_of_dist (μ := secBlockLaw p (seedsLaw (unitLaw N)) n)
      (Prod.fst : mBlock α γ (fun _ => Unit) n → _) K₀
    rw [hd] at h₂
    rw [hK₀B, h₂]
    exact hkey
  have hlogK := log_two_pow_ceil_le n hR
  have hlogK0 : 0 ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := log_natCast_nonneg _
  have hnode : ∀ k, I[c.keyB k : pair eveM c.transB ; secBlockLaw p (seedsLaw (unitLaw N)) n] ≤ n *
    ε ∧
      n * (R * log 2 - ε) ≤ H[c.keyB k ; secBlockLaw p (seedsLaw (unitLaw N)) n] := fun k => by
    obtain ⟨ht₁, ht₂⟩ := key_transfer hμ K₀B (c.keyB k) (pair eveM c.transB)
    have hF₁ := fano_weak hμ K₀B (c.keyB k) id
    have hF₂ := fano_weak hμ (c.keyB k) K₀B id
    rw [Fintype.card_fin] at hF₁ hF₂
    rw [errProb_symm] at hF₂
    exact oneWay_second_key hε₀0 hε₁ hε₂ hl.le hnε hlogK hlogK0 (hone k) hI₀ hH₀ ht₁ ht₂ hF₂ hF₁
  refine ⟨N, id, M, hM, fun _ => Unit, fun _ => inferInstance, unitLaw N, c, unitLaw_isPMF, ?_,
    fun j => (hnode j).1, fun j => (hnode j).2⟩
  refine le_trans ?_ (herr.trans (hsmall.trans (by linarith)))
  have h₂ := sum_dist_mul (secBlockLaw p (seedsLaw (unitLaw N)) n)
    (Prod.fst : mBlock α γ (fun _ => Unit) n → _) fun ω => ∑ k, Ind ω k
  rw [hd] at h₂
  refine le_trans ?_ (le_of_eq h₂.symm)
  simp only [MultiKeyCode.errProbB]
  refine sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (hμ.nonneg w)
  by_cases hex : ∃ j j', c.keyB j w ≠ c.keyB j' w
  · rw [ite_eq_left hex]
    obtain ⟨j, j', hne⟩ := hex
    have hbad : ∃ k, Ind w.1 k = 1 := by
      by_contra hall
      push Not at hall
      have hok : ∀ k, D k (fun i => (w.1 i).1 k) (fun i => (w.1 i).2)
          (manyBin B fun i => (w.1 i).1) = (fun i => (w.1 i).1) := fun k => by
        by_contra hk
        exact hall k (by simp [hInd, hk])
      apply hne
      rw [hKB j, hKB j']
      simp only [Function.comp, hok]
    obtain ⟨k, hk⟩ := hbad
    have := single_le_sum (f := fun k' => Ind w.1 k') (fun k' _ => hInd0 w.1 k') (mem_univ k)
    simp only [hk] at this
    exact this
  · rw [ite_eq_right hex]
    exact sum_nonneg fun k' _ => hInd0 w.1 k'

/-- The rate `0` is achievable with a protocol with no rounds and a constant key. -/
lemma isAchievableMultiKey_zero (hp : IsPMF p) : IsAchievableMultiKey p 0 := by
  refine ⟨le_rfl, fun ε hε => Eventually.of_forall fun n => ?_⟩
  have hK : 0 < 2 ^ ⌈(n : ℝ) * 0⌉₊ := by positivity
  set c : MultiKeyCode (spk := Fin.elim0) (M := fun _ : Fin 0 => 1) (2 ^ ⌈(n : ℝ) * 0⌉₊)
      (mObs α γ (fun _ => Unit) n) := ⟨fun l => l.elim0, fun _ _ _ => ⟨0, hK⟩⟩ with hc
  have hμ : IsPMF (secBlockLaw p (seedsLaw (unitLaw N)) n) :=
    secBlockLaw_isPMF hp (seedsLaw_isPMF unitLaw_isPMF) n
  have hconst : ∀ j, c.keyB j = fun _ => ⟨0, hK⟩ := fun j => rfl
  refine ⟨0, Fin.elim0, fun _ => 1, fun l => l.elim0, fun _ => Unit, fun _ => inferInstance,
    unitLaw N, c, unitLaw_isPMF, ?_, fun j => ?_, fun j => ?_⟩
  · have : c.errProbB (secBlockLaw p (seedsLaw (unitLaw N)) n) = 0 := by
      simp only [MultiKeyCode.errProbB, hconst]
      simp
    rw [this]
    exact hε.le
  · rw [hconst j, mutualInfo_eq_entropy_sub_condEntropy hμ, entropyRV_const hμ]
    have h₀ := condEntropy_nonneg hμ (fun _ : mBlock α γ (fun _ => Unit) n =>
      (⟨0, hK⟩ : Fin (2 ^ ⌈(n : ℝ) * 0⌉₊))) (pair eveM c.transB)
    have : (0 : ℝ) ≤ n * ε := by positivity
    linarith
  · have h₀ := entropyRV_nonneg hμ (c.keyB j)
    have : (0 : ℝ) ≤ n * ε := by positivity
    have e : (n : ℝ) * (0 * log 2 - ε) = -(n * ε) := by ring
    rw [e]
    linarith

/-- **Theorem 9 of Lecture 23 of [elgamal2010], page 23-54.** For `N ≥ 2`, when all the nodes know
`Z` the secret key capacity is `H(X^N | Z) - R_CFO([1 : N] | Z)`, in bits. -/
theorem multiKeyCapacity_eq (hp : IsPMF p) (hN : 2 ≤ N) :
    multiKeyCapacity p = H[Prod.fst | Prod.snd ; p] / log 2 - rCFOZ p := by
  have hN0 : 0 < N := by omega
  rw [← zCondH_univ hp]
  set v := zCondH p univ / log 2 - rCFOZ p with hv
  have hup : ∀ R ∈ {R | IsAchievableMultiKey p R}, R ≤ v := fun R hR => hR.le hp hN
  -- The rate `0` is achievable with a trivial protocol, so the value is nonnegative.
  have hv0 : 0 ≤ v := hup 0 (isAchievableMultiKey_zero hp)
  refine le_antisymm (Real.sSup_le hup hv0) ?_
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  rcases lt_or_ge r 0 with h0 | h0
  · exact h0.le.trans (Real.sSup_nonneg fun R hR => hR.1)
  · exact le_csSup ⟨_, hup⟩ (isAchievableMultiKey_of_lt hp hN0 h0 hr)

/-! ### The link with communication for omniscience -/

/-- **Page 23-54 of [elgamal2010].** The region is the region of communication for omniscience of
Lecture 21 for the sources `(Xⱼ, Z)`, in which all the nodes know `Z`. -/
theorem zRegion_eq_mwRegion (hp : IsPMF p) : zRegion p = mwRegion (zTuple p) univ := by
  classical
  ext R
  constructor
  · rintro ⟨h₀, h₁⟩
    refine ⟨h₀, fun k _ S hk => ?_⟩
    have hS : S ≠ univ := fun h => hk (h ▸ mem_univ k)
    rw [swCondH_zTuple hp hS]
    exact h₁ S hS
  · rintro ⟨h₀, h₁⟩
    refine ⟨h₀, fun S hS => ?_⟩
    obtain ⟨k, -, hk⟩ : ∃ k ∈ (univ : Finset (Fin N)), k ∉ S := by
      by_contra h
      push Not at h
      exact hS (eq_univ_of_forall fun j => h j (mem_univ j))
    rw [← swCondH_zTuple hp hS]
    exact h₁ k (mem_univ k) S hk

/-- **Page 23-54 of [elgamal2010].** `R_CFO([1 : N] | Z)` is the rate `R_CFO` of Lecture 21 for the
sources `(Xⱼ, Z)`. -/
theorem rCFOZ_eq_rCFO (hp : IsPMF p) : rCFOZ p = rCFO (zTuple p) univ := by
  rw [rCFOZ, rCFO, zRegion_eq_mwRegion hp]

end InfoTheory
