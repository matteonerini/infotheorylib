/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DFRun

/-!
# The decode–forward lower bound

Theorem 2 of Lecture 19 of El Gamal and Kim.

## Main definitions

* `dfInfo p W d`: `I(X^{d-1}; Y_d | X_d^N)`, in nats, where the nodes are numbered from `0`.

## Main statements

* `sum_dfE_eq`: **the chain rule of page 19-17**.
* `isAchievableMN_df`: **Theorem 2 of Lecture 19, the decode–forward lower bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section Info

variable {N : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  {p : (∀ l, X l) → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

/-- The nodes before node `d`. -/
def dfLt (d : Fin N) : Finset (Fin N) := univ.filter fun k => (k : ℕ) < d

/-- **Theorem 2 of Lecture 19 of [elgamal2010], page 19-8.** `I(X^{d-1}; Y_d | X_d^N)`, in nats. -/
def dfInfo (p : (∀ l, X l) → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (d : Fin N) : ℝ :=
  I[fun ω : (∀ l, X l) × (∀ l, Y l) => restr (dfLt d) ω.1 : fun ω => ω.2 d |
    fun ω => restr (dfLt d)ᶜ ω.1 ; jointOf p W]

lemma entropyRV_eq_of_comp₂ {Ω a b : Type*} [Fintype Ω] [Fintype a] [Fintype b] {μ : Ω → ℝ}
    (hμ : IsPMF μ) {A : Ω → a} {B : Ω → b} (f : b → a) (g : a → b) (hf : ∀ ω, A ω = f (B ω))
    (hg : ∀ ω, B ω = g (A ω)) : H[A ; μ] = H[B ; μ] := by
  have h₁ : A = f ∘ B := funext hf
  have h₂ : B = g ∘ A := funext hg
  refine le_antisymm ?_ ?_
  · rw [h₁]
    exact entropyRV_comp_le hμ B f
  · rw [h₂]
    exact entropyRV_comp_le hμ A g

variable [∀ k, DecidableEq (X k)] (d₀ : ∀ l, X l)

/-- The conditional entropy of the output of `d`, given the inputs from `t` on. -/
def dfH (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (d : Fin N) (t : ℕ) : ℝ :=
  H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | fun ω => fillGe d₀ t ω.1 ; L₀]

omit [∀ k, DecidableEq (X k)] in
/-- The exponent of the test is `I(X_k; Y_d | X_{k+1}^N) = H(Y_d | X_{k+1}^N) - H(Y_d | X_k^N)`. -/
lemma dfE_eq {L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ} (hL : IsPMF L₀) (k d : Fin N) :
    dfE d₀ L₀ k d = dfH d₀ L₀ d (k + 1) - dfH d₀ L₀ d k := by
  classical
  let F₁ : (∀ l, X l) × (∀ l, Y l) → ∀ l, X l := fun ω => fillGe d₀ (k + 1) ω.1
  let F₀ : (∀ l, X l) × (∀ l, Y l) → ∀ l, X l := fun ω => fillGe d₀ k ω.1
  let Yd : (∀ l, X l) × (∀ l, Y l) → Y d := fun ω => ω.2 d
  have hfill₁ : ∀ x : ∀ l, X l, fillGe d₀ (k + 1) (fillGe d₀ k x) = fillGe d₀ (k + 1) x := by
    intro x
    funext l
    simp only [fillGe]
    split_ifs with h₁ h₂
    · rfl
    · omega
    · rfl
  have hfill₂ : ∀ x : ∀ l, X l, Function.update (fillGe d₀ (k + 1) x) k (x k) = fillGe d₀ k x := by
    intro x
    funext l
    by_cases hl : l = k
    · subst hl
      simp [fillGe]
    · rw [Function.update_of_ne hl]
      have hne : (l : ℕ) ≠ k := fun e => hl (Fin.ext e)
      simp only [fillGe]
      by_cases hle : (k : ℕ) + 1 ≤ l
      · rw [ite_eq_left hle, ite_eq_left (by omega)]
      · rw [ite_eq_right hle, ite_eq_right (by omega)]
  have hkv : ∀ x : ∀ l, X l, fillGe d₀ k x k = x k := fun x => by simp [fillGe]
  have h₁ : H[Prod.fst ; dfLT d₀ L₀ k d] = H[pair F₁ Yd ; L₀] := by
    simp only [entropyRV, dfLT]
    rw [← dist_comp_eq]
    rfl
  have h₂ : H[fun z : ((∀ l, X l) × Y d) × X k => (z.1.1, z.2) ; dfLT d₀ L₀ k d] = H[F₀ ; L₀] := by
    have e : H[fun z : ((∀ l, X l) × Y d) × X k => (z.1.1, z.2) ; dfLT d₀ L₀ k d] =
        H[fun ω : (∀ l, X l) × (∀ l, Y l) => (F₁ ω, ω.1 k) ; L₀] := by
      simp only [entropyRV, dfLT]
      rw [← dist_comp_eq]
      rfl
    rw [e]
    refine entropyRV_eq_of_comp₂ hL (fun w => (fillGe d₀ (k + 1) w, w k))
      (fun t => Function.update t.1 k t.2) (fun ω => ?_) fun ω => ?_
    · simp only [F₁, F₀]
      rw [hfill₁, hkv]
    · simp only [F₁, F₀]
      rw [hfill₂]
  have h₃ : H[fun z : ((∀ l, X l) × Y d) × X k => z.1.1 ; dfLT d₀ L₀ k d] = H[F₁ ; L₀] := by
    simp only [entropyRV, dfLT]
    rw [← dist_comp_eq]
    rfl
  have h₄ : entropy (dfLT d₀ L₀ k d) = H[pair F₀ Yd ; L₀] := by
    have e : entropy (dfLT d₀ L₀ k d) =
        H[fun ω : (∀ l, X l) × (∀ l, Y l) => ((F₁ ω, Yd ω), ω.1 k) ; L₀] := rfl
    rw [e]
    refine entropyRV_eq_of_comp₂ hL (fun w => ((fillGe d₀ (k + 1) w.1, w.2), w.1 k))
      (fun t => (Function.update t.1.1 k t.2, t.1.2)) (fun ω => ?_) fun ω => ?_
    · simp only [F₁, F₀, pair]
      rw [hfill₁, hkv]
    · simp only [F₁, F₀, pair]
      rw [hfill₂]
  have h₅ : dfH d₀ L₀ d (k + 1) = H[pair F₁ Yd ; L₀] - H[F₁ ; L₀] := condEntropy_eq_sub hL _ _
  have h₆ : dfH d₀ L₀ d k = H[pair F₀ Yd ; L₀] - H[F₀ ; L₀] := condEntropy_eq_sub hL _ _
  rw [dfE, h₁, h₂, h₃, h₄, h₅, h₆]
  ring

omit [∀ k, DecidableEq (X k)] in
/-- **Page 19-17 of [elgamal2010]: the chain rule.**
`∑_{k < d} I(X_k; Y_d | X_{k+1}^N) = I(X^{d-1}; Y_d | X_d^N)`. -/
theorem sum_dfE_eq (hp : IsPMF p) (hW : IsChannel W) (d : Fin N) :
    ∑ k ∈ dfLt d, dfE d₀ (jointOf p W) k d = dfInfo p W d := by
  classical
  have hL := jointOf_isPMF hp hW
  set L₀ := jointOf p W with hL₀
  simp_rw [dfE_eq d₀ hL]
  have hsum : ∑ k ∈ dfLt d, (dfH d₀ L₀ d (k + 1) - dfH d₀ L₀ d k) =
      ∑ t ∈ range d, (dfH d₀ L₀ d (t + 1) - dfH d₀ L₀ d t) := by
    refine sum_bij (fun k _ => (k : ℕ)) (fun k hk => mem_range.mpr (mem_filter.mp hk).2)
      (fun a _ b _ h => Fin.ext h) (fun t ht => ?_) fun _ _ => rfl
    have ht' := mem_range.mp ht
    exact ⟨⟨t, ht'.trans d.2⟩, mem_filter.mpr ⟨mem_univ _, ht'⟩, rfl⟩
  rw [hsum, sum_range_sub]
  rw [dfInfo, condMutualInfo_comm hL, condMutualInfo_eq' hL]
  congr 1
  · refine (condEntropy_congr_right hL _
      (fun c : ∀ l : ((dfLt d)ᶜ : Finset (Fin N)), X l => (fun l =>
        if hl : l ∈ (dfLt d)ᶜ then c ⟨l, hl⟩ else d₀ l : ∀ l, X l)) (fun a b h => ?_) fun ω => ?_)
    · funext l
      have := congrFun h l
      simpa [l.2] using this
    · funext l
      by_cases hl : (d : ℕ) ≤ l
      · have hm : l ∈ (dfLt d)ᶜ := by
          simp only [dfLt, mem_compl, mem_filter, mem_univ, true_and, not_lt]
          exact hl
        simp only [fillGe]
        rw [ite_eq_left hl, dite_eq_left hm]
        rfl
      · have hm : l ∉ (dfLt d)ᶜ := by simpa [dfLt] using hl
        simp only [fillGe]
        rw [ite_eq_right hl, dite_eq_right hm]
  · have e₁ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | fun ω => fillGe d₀ 0 ω.1 ; L₀] =
        H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | Prod.fst ; L₀] := by
      refine condEntropy_congr_right hL _ id Function.injective_id fun ω => ?_
      funext l
      simp [fillGe]
    have e₂ : H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | pair (fun ω => restr (dfLt d)ᶜ ω.1)
        (fun ω => restr (dfLt d) ω.1) ; L₀] =
        H[fun ω : (∀ l, X l) × (∀ l, Y l) => ω.2 d | Prod.fst ; L₀] :=
      condEntropy_congr_right hL _ (fun x : ∀ l, X l => (restr (dfLt d)ᶜ x, restr (dfLt d) x))
        (restr_compl_restr_injective _) fun _ => rfl
    simp only [dfH]
    rw [e₁]
    exact e₂.symm

end Info

/-! ### A longer code -/

section Pad

variable {N Mm n B' t : ℕ} {X Y : Fin N → Type*} [NeZero Mm] [NeZero n] [∀ k, Fintype (X k)]
  [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] {M : Fin N → ℕ}
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

/-- **A longer code.** The rest of the symbols are not used, so the error is the same. -/
theorem dfCode_errProb_pad (hW : IsChannel W) (d₀ : ∀ l, X l) (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ)
    (ε : ℝ) (Cs : ℕ → DFBlock N Mm n X) (s₀ : Fin N) (e : Fin (M s₀) → Fin B' → Fin Mm)
    (dY : ∀ k, Y k) (hM : ∀ k, 0 < M k) (D : Fin N → Finset (Fin N)) (hb : B' + N ≤ t) {N' : ℕ}
    (hN : t * n ≤ N') :
    (dfCode d₀ L₀ ε Cs s₀ e dY hM N').errProb W D =
      (dfCode d₀ L₀ ε Cs s₀ e dY hM (t * n)).errProb W D := by
  classical
  set c' := dfCode d₀ L₀ ε Cs s₀ e dY hM N' with hc'
  set c := dfCode d₀ L₀ ε Cs s₀ e dY hM (t * n) with hc
  let T : (∀ k, Fin (M k)) × (Fin N' → ∀ k, Y k) → (∀ k, Fin (M k)) × (Fin (t * n) → ∀ k, Y k) :=
    fun z => (z.1, fun s => z.2 ⟨s, lt_of_lt_of_le s.2 hN⟩)
  have hlaw : dist (c'.law W) T = c.law W := dist_fbLaw_prefix hW (t * n) N' hN
  have hdec : ∀ z, c'.Wrong D z ↔ c.Wrong D (T z) := by
    intro z
    have hval : ∀ k, c'.dec k (z.1 k) (fun i => z.2 i k) =
      c.dec k (z.1 k) (fun i => (T z).2 i k) := by
      intro k
      have hE : (fun j : Fin B' => dfEst d₀ L₀ ε Cs B' k (getBlock (dY k) fun i => z.2 i k) j) =
          fun j : Fin B' => dfEst d₀ L₀ ε Cs B' k (getBlock (dY k) fun i => (T z).2 i k) j := by
        funext j
        refine dfEst_congr d₀ L₀ ε Cs B' k _ fun B hB => ?_
        have hBt : B < t := by
          have := j.2
          have := k.2
          omega
        funext i
        have hlt : i.val + n * B < t * n := by
          have h₁ : n * (B + 1) ≤ n * t := Nat.mul_le_mul_left _ hBt
          have h₂ := i.2
          rw [Nat.mul_add, Nat.mul_one] at h₁
          rw [Nat.mul_comm t n]
          omega
        have hlt' := lt_of_lt_of_le hlt hN
        simp only [getBlock, dite_eq_left hlt, dite_eq_left hlt']
        rfl
      simp only [hc', hc, dfCode]
      rw [hE]
    simp only [DMNCode.Wrong]
    refine exists_congr fun j => exists_congr fun k => and_congr_right fun _ => ?_
    rw [hval k]
  simp only [DMNCode.errProb]
  rw [← hlaw, sum_dist_mul]
  refine sum_congr rfl fun z _ => ?_
  congr 1
  simp only [ind, hdec z]

end Pad

/-! ### The coding theorem -/

section Theorem

variable {N : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  {p : (∀ l, X l) → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

set_option synthInstance.maxSize 1024 in
/-- **Theorem 2 of Lecture 19 of [elgamal2010], page 19-8: the decode–forward lower bound.** The
source is the node `s₀` numbered `0`. For every input law `p(xᴺ)`, the rate `R` is achievable if
`R < I(X^{d-1}; Y_d | X_d^N)` for all the nodes `d` other than the source, whatever the set `D` of
the destinations. -/
theorem isAchievableMN_df (hp : IsPMF p) (hW : IsChannel W) {s₀ : Fin N} (hs : (s₀ : ℕ) = 0)
    {D : Finset (Fin N)} (hD : ∀ k ∈ D, (k : ℕ) ≠ 0) {R : ℝ} (hR : 0 ≤ R)
    (hrate : ∀ d : Fin N, (d : ℕ) ≠ 0 → R * log 2 < dfInfo p W d) :
    IsAchievableMN W s₀ D R := by
  classical
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  set L₁ := jointOf p W with hL₁
  have hL₁P : IsPMF L₁ := jointOf_isPMF hp hW
  -- the alphabets are not empty
  obtain ⟨⟨d₀, dY⟩⟩ : Nonempty ((∀ l, X l) × (∀ l, Y l)) :=
    Fintype.card_pos_iff.mp (card_pos_of_isPMF hL₁P)
  -- the conditional laws
  have hκex : ∀ k, ∃ K : (∀ l, X l) → X k → ℝ, IsChannel K ∧
      ∀ c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * K c a := fun k => by
    have : Nonempty (X k) := ⟨d₀ k⟩
    exact exists_channel_of_joint (hp.dist _)
  choose κ hκc hκ using hκex
  -- the slack in the rate
  obtain ⟨ξ, hξ, hslack₀⟩ := exists_pos_le_of_finite (ι := Fin N)
    (g := fun d => if (d : ℕ) ≠ 0 then dfInfo p W d - R * log 2 else 1) (fun d => by
      split_ifs with h
      · have := hrate d h
        linarith
      · exact one_pos)
  have hslack : ∀ d : Fin N, (d : ℕ) ≠ 0 → R * log 2 + 3 * (ξ / 3) ≤ dfInfo p W d := by
    intro d hd
    have := hslack₀ d
    rw [ite_eq_left hd] at this
    linarith
  set ξ₃ := ξ / 3 with hξ₃
  have hξ₃0 : 0 < ξ₃ := by positivity
  -- the typicality parameter
  set Cmax := ∑ d : Fin N, ∑ k ∈ dfLt d, |dfC d₀ L₁ k d| with hCmax
  have hCm0 : 0 ≤ Cmax := sum_nonneg fun d _ => sum_nonneg fun k _ => abs_nonneg _
  set ε := ξ₃ / (Cmax + 1) with hεd
  have hε : 0 < ε := by positivity
  have hEd : ∀ d : Fin N, (d : ℕ) ≠ 0 → R * log 2 + 2 * ξ₃ ≤ dfEd d₀ L₁ ε d := by
    intro d hd
    have h₁ := hslack d hd
    have h₂ := sum_dfE_eq d₀ hp hW d
    have h₃ : ∑ k ∈ dfLt d, dfC d₀ L₁ k d ≤ Cmax := by
      refine (sum_le_sum fun k _ => le_abs_self _).trans ?_
      exact single_le_sum (f := fun d => ∑ k ∈ dfLt d, |dfC d₀ L₁ k d|)
        (fun d _ => sum_nonneg fun k _ => abs_nonneg _) (mem_univ d)
    have h₄ : ε * ∑ k ∈ dfLt d, dfC d₀ L₁ k d ≤ ξ₃ := by
      calc _ ≤ ε * (Cmax + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
        _ = ξ₃ := by
            rw [hεd]
            field_simp
    have h₅ : dfEd d₀ L₁ ε d = dfInfo p W d - ε * ∑ k ∈ dfLt d, dfC d₀ L₁ k d := by
      rw [dfEd, sum_sub_distrib, mul_sum, ← h₂]
      rfl
    rw [h₅]
    linarith
  -- the parameters
  set r := R * log 2 with hr
  have hr0 : 0 ≤ r := mul_nonneg hR hlog.le
  obtain ⟨B', hB'⟩ : ∃ B' : ℕ, (N : ℝ) * r + 1 ≤ B' * ξ₃ := by
    obtain ⟨s, hs'⟩ := exists_nat_ge (((N : ℝ) * r + 1) / ξ₃)
    exact ⟨s, (div_le_iff₀ hξ₃0).mp hs'⟩
  set t := B' + N with ht
  have htpos : 0 < t + 1 := by omega
  let Mn : ℕ → ℕ := fun n => ⌈exp (n * (r + ξ₃))⌉₊
  have hMn0 : ∀ n, NeZero (Mn n) := fun n => ⟨(Nat.ceil_pos.mpr (exp_pos _)).ne'⟩
  have hρ0 : 0 ≤ r + ξ₃ := by positivity
  have hMnle : ∀ n : ℕ, (Mn n : ℝ) ≤ 2 * exp (n * (r + ξ₃)) := by
    intro n
    have h₁ : 1 ≤ exp ((n : ℝ) * (r + ξ₃)) := one_le_exp (mul_nonneg (Nat.cast_nonneg n) hρ0)
    have h₂ := Nat.ceil_lt_add_one (exp_pos ((n : ℝ) * (r + ξ₃))).le
    simp only [Mn]
    linarith
  have hMnge : ∀ n : ℕ, exp (n * (r + ξ₃)) ≤ Mn n := fun n => Nat.le_ceil _
  -- the error for each length
  have hdef : ∀ N' : ℕ, Nonempty (DMNCode (fun k => 2 ^ ⌈(N' : ℝ) * mcRate s₀ R k⌉₊) N' X Y) :=
    fun N' => ⟨⟨fun k _ _ _ => d₀ k, fun _ _ _ j => ⟨0, by positivity⟩⟩⟩
  have hsmall : ∀ η > 0, ∀ᶠ N' : ℕ in atTop,
      ∃ c : DMNCode (fun k => 2 ^ ⌈(N' : ℝ) * mcRate s₀ R k⌉₊) N' X Y,
        c.errProb W (mcDest s₀ D) ≤ η := by
    intro η hη
    have hlim := tendsto_prob_robustTypicalSet hL₁P hε
    have hexp : Tendsto (fun n : ℕ => exp (-(n * ξ₃))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const hξ₃0)
    have htail : ∀ᶠ n : ℕ in atTop, (N : ℝ) * (B' * (2 * exp (-(n * ξ₃)))) ≤ η / 2 := by
      have h₁ : Tendsto (fun n : ℕ => (N : ℝ) * (B' * (2 * exp (-(n * ξ₃))))) atTop
          (𝓝 ((N : ℝ) * (B' * (2 * 0)))) :=
        ((hexp.const_mul 2).const_mul _).const_mul _
      simp only [mul_zero] at h₁
      filter_upwards [(tendsto_order.1 h₁).2 (η / 2) (by positivity)] with n hn using hn.le
    have hbig : ∀ᶠ n : ℕ in atTop,
        ((t : ℝ) + 0) * r + log 2 ≤ n ∧ 0 < n := by
      filter_upwards [eventually_ge_atTop ⌈(t : ℝ) * r + log 2⌉₊, eventually_gt_atTop 0]
        with n hn hn₀
      refine ⟨?_, hn₀⟩
      have := Nat.ceil_le.mp hn
      simpa using this
    have hηb : ∀ᶠ n : ℕ in atTop, ((t : ℝ)) * (1 - prob (iidPMF L₁ n) (robustTypicalSet L₁ n ε)) ≤
        η / 2 := by
      have h₁ : Tendsto (fun n : ℕ => (t : ℝ) * (1 - prob (iidPMF L₁ n)
          (robustTypicalSet L₁ n ε))) atTop (𝓝 ((t : ℝ) * (1 - 1))) :=
        (tendsto_const_nhds.sub hlim).const_mul _
      simp only [sub_self, mul_zero] at h₁
      filter_upwards [(tendsto_order.1 h₁).2 (η / 2) (by positivity)] with n hn using hn.le
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (htail.and (hbig.and hηb))
    refine eventually_atTop.mpr ⟨t * n₀ + t + 1, fun N' hN' => ?_⟩
    have htp : 0 < t + 1 := htpos
    set n := N' / t with hn
    have htn0 : 0 < t := by
      have := s₀.2
      omega
    have hnge : n₀ ≤ n := by
      rw [hn, Nat.le_div_iff_mul_le htn0]
      calc n₀ * t = t * n₀ := Nat.mul_comm _ _
        _ ≤ N' := by omega
    obtain ⟨htailn, ⟨hbign, hnpos⟩, hηn⟩ := hn₀ n hnge
    have : NeZero n := ⟨hnpos.ne'⟩
    have : NeZero (Mn n) := hMn0 n
    have htN : t * n ≤ N' := by
      rw [hn]
      exact Nat.mul_div_le N' t
    have hNlt : (N' : ℝ) < t * ((n : ℝ) + 1) := by
      have h₁ : N' < t * (n + 1) := by
        rw [hn]
        exact Nat.lt_mul_div_succ N' htn0
      exact_mod_cast h₁
    set M : Fin N → ℕ := fun k => 2 ^ ⌈(N' : ℝ) * mcRate s₀ R k⌉₊ with hMd
    have hMpos : ∀ k, 0 < M k := fun k => by
      simp only [hMd]
      positivity
    -- the messages fit in the blocks
    have hfit : M s₀ ≤ (Mn n) ^ B' := by
      have hR' : mcRate s₀ R s₀ = R := by simp [mcRate]
      have h₁ : ((M s₀ : ℕ) : ℝ) = exp ((⌈(N' : ℝ) * R⌉₊ : ℝ) * log 2) := by
        simp only [hMd, hR']
        push_cast
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      have hN0 : (0 : ℝ) ≤ (N' : ℝ) * R := mul_nonneg (Nat.cast_nonneg _) hR
      have h₂ := (Nat.ceil_lt_add_one hN0).le
      have h₃ : (N' : ℝ) * R ≤ t * ((n : ℝ) + 1) * R := mul_le_mul_of_nonneg_right hNlt.le hR
      have h₄ : ((M s₀ : ℕ) : ℝ) ≤ exp (B' * ((n : ℝ) * (r + ξ₃))) := by
        rw [h₁]
        refine exp_le_exp.mpr ?_
        have h₅ : (⌈(N' : ℝ) * R⌉₊ : ℝ) * log 2 ≤ ((t : ℝ) * ((n : ℝ) + 1) * R + 1) * log 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hlog.le
        have htc : (t : ℝ) = B' + N := by
          rw [ht]
          push_cast
          ring
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have h₆ : ((n : ℝ)) * ((N : ℝ) * r + 1) ≤ n * (B' * ξ₃) :=
          mul_le_mul_of_nonneg_left hB' hn0
        have h₇ : ((t : ℝ) + 0) * r + log 2 ≤ n := hbign
        have h₈ : ((t : ℝ) * ((n : ℝ) + 1) * R + 1) * log 2 = (t : ℝ) * n * r + (t : ℝ) * r +
          log 2 := by
          rw [hr]
          ring
        rw [h₈] at h₅
        rw [htc] at h₅ h₇
        nlinarith
      have h₅ : exp (B' * ((n : ℝ) * (r + ξ₃))) ≤ ((Mn n ^ B' : ℕ) : ℝ) := by
        push_cast
        rw [exp_nat_mul]
        exact pow_le_pow_left₀ (exp_pos _).le (hMnge n) B'
      exact_mod_cast h₄.trans h₅
    obtain ⟨ef⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (M s₀))
      (β := Fin B' → Fin (Mn n)) (by simpa using hfit)
    let dξ : DFΞ N (Mn n) n X Y := (fun k _ _ _ => d₀ k, fun _ => dY)
    set e := exp (-((n : ℝ) * (r + 2 * ξ₃))) with he
    have hed : ∀ d : Fin N, (d : ℕ) ≠ 0 → exp (-((n : ℝ) * dfEd d₀ L₁ ε d)) ≤ e := by
      intro d hd
      refine exp_le_exp.mpr ?_
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have := mul_le_mul_of_nonneg_left (hEd d hd) hn0
      linarith
    have havg := dfCode_avg_le (t := t) (M := M) (Mm := Mn n) (n := n) (κ := κ) (B' := B') (Y := Y)
      d₀ hp hW hκc hκ ε le_rfl dξ hs ef.injective dY hMpos hD hed (exp_pos _).le
    have hlaw : IsPMF (piLaw fun _ : Fin t => dfBlockLaw (X := X) κ (Mn n) n) :=
      piLaw_isPMF fun _ => dfBlockLaw_isPMF hκc
    obtain ⟨Cst, hC⟩ := exists_le_of_sum_mul_le hlaw havg
    refine ⟨dfCode d₀ L₁ ε (arrOf dξ.1 Cst) s₀ ef dY hMpos N', ?_⟩
    rw [dfCode_errProb_pad hW d₀ L₁ ε _ s₀ ef dY hMpos _ le_rfl htN]
    refine hC.trans ?_
    have hMe : (Mn n : ℝ) * e ≤ 2 * exp (-((n : ℝ) * ξ₃)) := by
      calc (Mn n : ℝ) * e ≤ 2 * exp (n * (r + ξ₃)) * e :=
            mul_le_mul_of_nonneg_right (hMnle n) (exp_pos _).le
        _ = _ := by
            rw [he, mul_assoc, ← exp_add]
            congr 2
            ring
    have h₁ : (N : ℝ) * (B' * ((Mn n : ℝ) * e)) ≤ (N : ℝ) * (B' * (2 * exp (-((n : ℝ) * ξ₃)))) := by
      gcongr
    linarith
  obtain ⟨c, hc⟩ := exists_seq_tendsto (C := fun N' : ℕ =>
    DMNCode (fun k => 2 ^ ⌈(N' : ℝ) * mcRate s₀ R k⌉₊) N' X Y)
    (fun N' c => c.errProb W (mcDest s₀ D)) (fun N' c => by
      have hμ := c.law_isPMF (fun k => by positivity) hW
      exact sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (ind_nonneg _)) hsmall
  exact ⟨c, hc⟩

end Theorem

end InfoTheory
