/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.Wiretap

/-!
# The wiretap channel: achievability and the secrecy capacity

Theorem 3 of Lecture 23 of El Gamal and Kim. We generate i.i.d. codewords `uⁿ(m, l)`, with `L`
values of `l` in the bin of the message `m`. To send `m`, the encoder picks `l` at random and sends
`Xⁿ` from `uⁿ(m, l)` through the channel `p(x | u)`.

## Main definitions

* `eveDec`, `wiretapCodeOf`: the decoder of the eavesdropper in a bin, and the code of a codebook.

## Main statements

* `sum_iidPMF_comp_injective`: a part of an i.i.d. codebook is an i.i.d. codebook.
* `exists_wiretap_code_le`: the bounds for one code, from a random codebook.
* `isAchievableWiretap_of_lt`: the achievability.
* `wiretapCapacity_eq`: **Theorem 3 of Lecture 23**: `C_S = max_{p(u, x)} (I(U; Y) - I(U; Z))`.

## Implementation notes

The notes take a bin rate `R̃ - R > I(U; Z)` and bound `H(L | Zⁿ, M)` with Chebyshev's inequality on
the number of typical codewords in a bin (Lemma 1 of page 23-17). We take the bin rate just below
`I(U; Z)`, which is Wyner's original choice. The eavesdropper can then decode `L` given `M`, by the
packing lemma, and Fano's inequality bounds `H(L | Zⁿ, M)`. No second-moment argument is needed.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### A part of an i.i.d. codebook -/

section Part

variable {X : Type*} [Fintype X]

/-- A part of an i.i.d. codebook is an i.i.d. codebook. -/
lemma sum_iidPMF_comp_injective {μ : X → ℝ} (hμ : IsPMF μ) {M L : ℕ} (e : Fin L → Fin M)
    (he : Function.Injective e) (g : (Fin L → X) → ℝ) :
    ∑ C : Fin M → X, iidPMF μ M C * g (C ∘ e) = ∑ D, iidPMF μ L D * g D := by
  classical
  have h₁ : ∀ D : Fin L → X, ∑ C : Fin M → X, iidPMF μ M C * (if C ∘ e = D then 1 else 0) =
      iidPMF μ L D := fun D => by
    set a : Fin M → X → ℝ := fun i x => if h : ∃ l, e l = i then
      (if x = D h.choose then 1 else 0) else 1 with ha
    have hC : ∀ C : Fin M → X, (if C ∘ e = D then (1 : ℝ) else 0) = ∏ i, a i (C i) := fun C => by
      by_cases h : C ∘ e = D
      · have e₀ : (if C ∘ e = D then (1 : ℝ) else 0) = 1 := by simp [h]
        rw [e₀]
        symm
        refine prod_eq_one fun i _ => ?_
        simp only [ha]
        split_ifs with hi hx
        · rfl
        · exact absurd (by rw [← h, Function.comp, hi.choose_spec]) hx
        · rfl
      · have e₀ : (if C ∘ e = D then (1 : ℝ) else 0) = 0 := by simp [h]
        rw [e₀]
        symm
        obtain ⟨l, hl⟩ : ∃ l, C (e l) ≠ D l := by
          by_contra hne
          push Not at hne
          exact h (funext hne)
        refine prod_eq_zero (mem_univ (e l)) ?_
        have hex : ∃ l', e l' = e l := ⟨l, rfl⟩
        have hc : hex.choose = l := he hex.choose_spec
        have hai : a (e l) (C (e l)) = if C (e l) = D hex.choose then 1 else 0 := by
          simp only [ha]
          exact dite_eq_left_of_eq_true (eq_true hex)
        rw [hai, hc]
        simp [hl]
    calc ∑ C : Fin M → X, iidPMF μ M C * (if C ∘ e = D then 1 else 0)
        = ∑ C : Fin M → X, ∏ i, (μ (C i) * a i (C i)) :=
          sum_congr rfl fun C _ => by rw [hC, iidPMF, prod_mul_distrib]
      _ = ∏ i, ∑ x, (μ x * a i x) := (Fintype.prod_sum fun i x => μ x * a i x).symm
      _ = iidPMF μ L D := by
          rw [iidPMF]
          refine (Fintype.prod_of_injective e he _ _ (fun i hi => ?_) fun l => ?_).symm
          · have hn : ¬∃ l, e l = i := fun ⟨l, hl⟩ => hi ⟨l, hl⟩
            simp [ha, hn, hμ.sum_eq_one]
          · have hex : ∃ l', e l' = e l := ⟨l, rfl⟩
            have hc : hex.choose = l := he hex.choose_spec
            simp [ha, hc]
  have h₂ : ∀ C : Fin M → X, g (C ∘ e) = ∑ D, g D * (if C ∘ e = D then 1 else 0) := fun C => by
    simp
  simp only [h₂, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun D _ => ?_
  rw [← h₁, sum_mul]
  exact sum_congr rfl fun C _ => by ring

end Part

/-! ### Averages over a random codebook -/

section Average

variable {𝒰 β γ : Type*} [Fintype 𝒰] [Fintype β] [Fintype γ]

/-- The average probability of error, averaged over the random codebooks. -/
lemma sum_codebook_avgErr_le {p : 𝒰 → ℝ} (hp : IsPMF p) {V : 𝒰 → β → ℝ} (hV : IsChannel V)
    {n M : ℕ} (ε : ℝ) (w₀ : Fin M) :
    ∑ C : Fin M → Fin n → 𝒰, iidPMF (iidPMF p n) M C *
        (typicalCode (jointTypicalSet (jointOf p V) n ε) C w₀).avgErrProb V ≤
      (1 - prob (jointIid (jointOf p V) n) (jointTypicalSet (jointOf p V) n ε)) +
        (M - 1) * exp (-(n * (mutualInfoOf p V - 3 * ε))) := by
  have hM : 0 < M := w₀.pos
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  set U := (1 - prob (jointIid (jointOf p V) n) (jointTypicalSet (jointOf p V) n ε)) +
    (M - 1) * exp (-(n * (mutualInfoOf p V - 3 * ε)))
  simp only [ChannelCode.avgErrProb, mul_div_assoc', ← sum_div, mul_sum]
  rw [sum_comm, div_le_iff₀ hM']
  calc ∑ w : Fin M, ∑ C : Fin M → Fin n → 𝒰, iidPMF (iidPMF p n) M C *
        (typicalCode (jointTypicalSet (jointOf p V) n ε) C w₀).condErrProb V w
      ≤ ∑ _w : Fin M, U := sum_le_sum fun w _ => sum_codebook_condErrProb_le hp hV ε w₀ w
    _ = U * M := by simp [mul_comm]

/-- `H(Zⁿ | Uⁿ) = n H(Z | U)`, for an i.i.d. input. -/
lemma sum_iidPMF_entropy_channelExt {p : 𝒰 → ℝ} (hp : IsPMF p) {V : 𝒰 → γ → ℝ} (hV : IsChannel V)
    (n : ℕ) :
    ∑ x, iidPMF p n x * entropy (channelExt V n x) = n * ∑ u, p u * entropy (V u) := by
  have hq := jointOf_isPMF hp hV
  have h₁ := condEntropy_jointIid_snd hq n
  rw [condEntropy_jointOf hp hV] at h₁
  have hL : jointIid (jointOf p V) n = jointOf (iidPMF p n) (channelExt V n) :=
    funext fun z => jointIid_jointOf p V n z
  rw [hL, condEntropy_jointOf (iidPMF_isPMF hp n) (hV.ext n)] at h₁
  exact h₁

variable {M L n : ℕ}

/-- The output law of the `M L` codewords, each with the same probability. -/
def codebookOut (V : 𝒰 → γ → ℝ) (C : Fin M → Fin n → 𝒰) (z : Fin n → γ) : ℝ :=
  (1 / M) * ∑ w, channelExt V n (C w) z

/-- `I(L; Zⁿ)` for a fixed codebook: `H(Zⁿ) - H(Zⁿ | L)`. -/
def codebookInfo (V : 𝒰 → γ → ℝ) (C : Fin M → Fin n → 𝒰) : ℝ :=
  entropy (codebookOut V C) - (1 / M) * ∑ w, entropy (channelExt V n (C w))

/-- **The bound `I(L; Zⁿ | 𝒞) ≤ n I(U; Z)` of page 23-16 of [elgamal2010].** -/
lemma sum_codebook_codebookInfo_le {p : 𝒰 → ℝ} (hp : IsPMF p) {V : 𝒰 → γ → ℝ} (hV : IsChannel V)
    (hM : 0 < M) :
    ∑ C : Fin M → Fin n → 𝒰, iidPMF (iidPMF p n) M C * codebookInfo V C ≤
      n * mutualInfoOf p V := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hpn := iidPMF_isPMF hp n
  have hlaw := iidPMF_isPMF hpn M
  have hO : IsChannel fun C : Fin M → Fin n → 𝒰 => codebookOut V C := fun C => by
    refine ⟨fun z => mul_nonneg (by positivity)
      (sum_nonneg fun w _ => channelExt_nonneg hV _ _), ?_⟩
    simp only [codebookOut, ← mul_sum]
    rw [sum_comm]
    simp only [((hV.ext n) _).sum_eq_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- The law of `Zⁿ` is i.i.d.
  have hd : outDist (iidPMF (iidPMF p n) M) (fun C => codebookOut V C) =
      iidPMF (outDist p V) n := by
    funext z
    have hone : ∀ w : Fin M, ∑ C : Fin M → Fin n → 𝒰,
        iidPMF (iidPMF p n) M C * (1 / (M : ℝ) * channelExt V n (C w) z) =
          1 / (M : ℝ) * iidPMF (outDist p V) n z := fun w => by
      rw [sum_iidPMF_eval hpn w fun x => 1 / (M : ℝ) * channelExt V n x z,
        ← sum_iidPMF_mul_channelExt p V n z, mul_sum]
      exact sum_congr rfl fun x _ => by ring
    calc outDist (iidPMF (iidPMF p n) M) (fun C => codebookOut V C) z
        = ∑ w : Fin M, ∑ C : Fin M → Fin n → 𝒰,
            iidPMF (iidPMF p n) M C * (1 / (M : ℝ) * channelExt V n (C w) z) := by
          simp only [outDist, codebookOut, mul_sum]
          exact sum_comm
      _ = _ := by
          simp only [hone, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  -- Concavity of the entropy, as `H(Zⁿ | 𝒞) ≤ H(Zⁿ)`.
  have hconc : ∑ C : Fin M → Fin n → 𝒰, iidPMF (iidPMF p n) M C * entropy (codebookOut V C) ≤
      n * entropy (outDist p V) := by
    have h₁ := condEntropy_le_entropy (jointOf_isPMF hlaw hO) Prod.snd Prod.fst
    rw [condEntropy_jointOf hlaw hO, entropyRV, dist_jointOf_snd, hd,
      entropy_iidPMF (outDist_isPMF hp hV)] at h₁
    exact h₁
  have hcond : ∑ C : Fin M → Fin n → 𝒰, iidPMF (iidPMF p n) M C *
      ((1 / M : ℝ) * ∑ w, entropy (channelExt V n (C w))) =
      n * ∑ u, p u * entropy (V u) := by
    simp only [mul_sum]
    rw [sum_comm]
    have : ∀ w : Fin M, ∑ C : Fin M → Fin n → 𝒰,
        iidPMF (iidPMF p n) M C * (1 / (M : ℝ) * entropy (channelExt V n (C w))) =
          1 / (M : ℝ) * (n * ∑ u, p u * entropy (V u)) := fun w => by
      have h₁ := sum_iidPMF_eval hpn w fun x => 1 / (M : ℝ) * entropy (channelExt V n x)
      rw [h₁, ← sum_iidPMF_entropy_channelExt hp hV n, mul_sum]
      exact sum_congr rfl fun x _ => by ring
    simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
    field_simp
  simp only [codebookInfo, mul_sub]
  rw [sum_sub_distrib, mutualInfoOf_eq hp hV, mul_sub, hcond]
  linarith

end Average

/-! ### The code of a codebook -/

section Code

variable {α β γ 𝒰 : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype 𝒰] {M L n : ℕ}
  {W : α → β × γ → ℝ} {r : 𝒰 → α → ℝ}

omit [Fintype β] [Fintype 𝒰] in
/-- The sum over the inputs of a channel `T` after a kernel `r`. -/
lemma sum_channelExt_throughKernel (r : 𝒰 → α → ℝ) (T : α → β → ℝ) (u : Fin n → 𝒰) (y : Fin n → β) :
    ∑ x, channelExt r n u x * channelExt T n x y = channelExt (throughKernel r T) n u y := by
  simp only [channelExt, ← prod_mul_distrib, throughKernel, outDist]
  exact (Fintype.prod_sum fun i a => r (u i) a * T a (y i)).symm

/-- The index of the codeword `uⁿ(m, l)`. -/
def binIdx (M L : ℕ) (m : Fin M) (l : Fin L) : Fin (M * L) := finProdFinEquiv (m, l)

lemma binIdx_injective (M L : ℕ) (m : Fin M) : Function.Injective (binIdx M L m) := fun a b h => by
  have := finProdFinEquiv.injective h
  simpa using this

/-- **Page 23-14 of [elgamal2010].** The code of a codebook `C` and of a decoder `d` of the index of
the codeword. To send `m`, the encoder picks `l` uniformly at random and sends `Xⁿ` from `uⁿ(m, l)`
through `p(x | u)`. The decoder declares the bin index of `d(yⁿ)`. -/
def wiretapCodeOf [NeZero L] (hr : IsChannel r) (C : Fin (M * L) → Fin n → 𝒰)
    (d : (Fin n → β) → Fin (M * L)) : WiretapCode M n α β where
  enc m x := (1 / L) * ∑ l, channelExt r n (C (binIdx M L m l)) x
  isChannel_enc m := by
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
    refine ⟨fun x => mul_nonneg (by positivity)
      (sum_nonneg fun l _ => channelExt_nonneg hr _ _), ?_⟩
    simp only [← mul_sum]
    rw [sum_comm]
    simp only [((hr.ext n) _).sum_eq_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  dec y := (finProdFinEquiv.symm (d y)).1

variable [NeZero M] [NeZero L] (hr : IsChannel r) (C : Fin (M * L) → Fin n → 𝒰)
  (d : (Fin n → β) → Fin (M * L))

omit [Fintype 𝒰] in
/-- The sum over the law of the code of a function of the message and `Yⁿ`. -/
lemma sum_wiretapCodeOf_law_Y [Finite 𝒰] (f : Fin M → (Fin n → β) → ℝ) :
    ∑ z, (wiretapCodeOf hr C d).law W z * f z.1.1 (WiretapCode.outY z) =
      (1 / (M * L)) * ∑ m, ∑ l, ∑ y,
        channelExt (throughKernel r (bcMarg₁ W)) n (C (binIdx M L m l)) y * f m y := by
  have := Fintype.ofFinite 𝒰
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  simp only [Fintype.sum_prod_type]
  have hoY : ∀ (a : Fin M × (Fin n → α)) (t : Fin n → β × γ),
      WiretapCode.outY (a, t) = fun i => (t i).1 := fun _ _ => rfl
  simp only [WiretapCode.law, WiretapCode.inputLaw, jointOf, uniformPMF, Fintype.card_fin, hoY,
    mul_sum]
  refine sum_congr rfl fun m _ => ?_
  have h₁ : ∀ x, ∑ t : Fin n → β × γ, 1 / (M : ℝ) * (wiretapCodeOf hr C d).enc m x *
      channelExt W n x t * f m (fun i => (t i).1) =
      1 / (M : ℝ) * (wiretapCodeOf hr C d).enc m x *
        ∑ y, channelExt (bcMarg₁ W) n x y * f m y := fun x => by
    rw [← sum_channelExt_fst W x (f m), mul_sum]
    exact sum_congr rfl fun t _ => by ring
  simp only [h₁]
  have step : ∀ x, 1 / (M : ℝ) * (wiretapCodeOf hr C d).enc m x *
      ∑ y, channelExt (bcMarg₁ W) n x y * f m y =
      ∑ l, ∑ y, 1 / ((M : ℝ) * L) * (channelExt r n (C (binIdx M L m l)) x *
        (channelExt (bcMarg₁ W) n x y * f m y)) := fun x => by
    change 1 / (M : ℝ) * ((1 / (L : ℝ)) * ∑ l, channelExt r n (C (binIdx M L m l)) x) * _ = _
    rw [show ∀ S T : ℝ, 1 / (M : ℝ) * ((1 / (L : ℝ)) * S) * T = 1 / ((M : ℝ) * L) * (S * T) from
      fun S T => by field_simp, sum_mul, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_sum, mul_sum]
  simp only [step]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← sum_channelExt_throughKernel, sum_mul, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  ring

omit [Fintype 𝒰] in
/-- The law of `(M, Zⁿ)` of the code. -/
lemma dist_wiretapCodeOf_Z [Finite 𝒰] (m : Fin M) (z : Fin n → γ) :
    dist ((wiretapCodeOf hr C d).law W) (pair (fun w => w.1.1) WiretapCode.outZ) (m, z) =
      (1 / (M * L)) * ∑ l, channelExt (throughKernel r (bcMarg₂ W)) n (C (binIdx M L m l)) z := by
  have := Fintype.ofFinite 𝒰
  classical
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h₀ : dist ((wiretapCodeOf hr C d).law W) (pair (fun w => w.1.1) WiretapCode.outZ) (m, z) =
      ∑ x, 1 / (M : ℝ) * (wiretapCodeOf hr C d).enc m x * channelExt (bcMarg₂ W) n x z := by
    simp only [dist, pair, Prod.mk.injEq, Fintype.sum_prod_type]
    rw [sum_eq_single m (fun b _ hb => by simp [hb]) (by simp)]
    refine sum_congr rfl fun x _ => ?_
    have h₂ := sum_channelExt_snd W x fun y => if y = z then (1 : ℝ) else 0
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true] at h₂
    rw [← h₂, mul_sum]
    refine sum_congr rfl fun t _ => ?_
    simp only [WiretapCode.law, WiretapCode.inputLaw, jointOf, uniformPMF, Fintype.card_fin]
    by_cases h : (fun i => (t i).2) = z
    · rw [ite_eq_left ⟨trivial, h⟩, ite_eq_left h]
    · rw [ite_eq_right fun hh => h hh.2, ite_eq_right h, mul_zero]
  rw [h₀]
  have step : ∀ x, 1 / (M : ℝ) * (wiretapCodeOf hr C d).enc m x * channelExt (bcMarg₂ W) n x z =
      ∑ l, 1 / ((M : ℝ) * L) * (channelExt r n (C (binIdx M L m l)) x *
        channelExt (bcMarg₂ W) n x z) := fun x => by
    change 1 / (M : ℝ) * ((1 / (L : ℝ)) * ∑ l, channelExt r n (C (binIdx M L m l)) x) * _ = _
    rw [show ∀ S T : ℝ, 1 / (M : ℝ) * ((1 / (L : ℝ)) * S) * T = 1 / ((M : ℝ) * L) * (S * T) from
      fun S T => by field_simp, sum_mul, mul_sum]
  simp only [step]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [← sum_channelExt_throughKernel, mul_sum]

omit [Fintype 𝒰] in
/-- **Page 23-15 of [elgamal2010].** The probability of error of the code is at most the average
probability of error of decoding the index of the codeword. -/
lemma errProb_wiretapCodeOf_le [Finite 𝒰] (hr' : IsChannel (throughKernel r (bcMarg₁ W))) :
    (wiretapCodeOf hr C d).errProb W ≤
      (ChannelCode.mk C d).avgErrProb (throughKernel r (bcMarg₁ W)) := by
  have := Fintype.ofFinite 𝒰
  classical
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h₁ : (wiretapCodeOf hr C d).errProb W = ∑ z, (wiretapCodeOf hr C d).law W z *
      (fun (m : Fin M) (y : Fin n → β) =>
        if (wiretapCodeOf hr C d).dec y ≠ m then (1 : ℝ) else 0) z.1.1 (WiretapCode.outY z) := by
    simp only [WiretapCode.errProb, InfoTheory.errProb]
    refine sum_congr rfl fun z _ => ?_
    split_ifs <;> simp
  rw [h₁, sum_wiretapCodeOf_law_Y hr C d fun m y =>
    if (wiretapCodeOf hr C d).dec y ≠ m then (1 : ℝ) else 0]
  simp only [ChannelCode.avgErrProb, ChannelCode.condErrProb]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have hle : ∀ m l, ∑ y, channelExt (throughKernel r (bcMarg₁ W)) n (C (binIdx M L m l)) y *
      (if (wiretapCodeOf hr C d).dec y ≠ m then (1 : ℝ) else 0) ≤
      ∑ y, if d y ≠ finProdFinEquiv (m, l) then
        channelExt (throughKernel r (bcMarg₁ W)) n (C (finProdFinEquiv (m, l))) y else 0 := by
    intro m l
    refine sum_le_sum fun y _ => ?_
    by_cases hd : d y = finProdFinEquiv (m, l)
    · have : (wiretapCodeOf hr C d).dec y = m := by
        change (finProdFinEquiv.symm (d y)).1 = m
        rw [hd, Equiv.symm_apply_apply]
      simp [this, hd]
    · have h0 : 0 ≤ channelExt (throughKernel r (bcMarg₁ W)) n (C (finProdFinEquiv (m, l))) y :=
        channelExt_nonneg hr' _ y
      simp only [hd, ne_eq, not_false_eq_true, ite_true]
      split_ifs <;> simp [binIdx, h0]
  have hpos : (0 : ℝ) < M * L := by
    have h₂ : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
    have h₃ : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  push_cast
  rw [one_div, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (sum_le_sum fun m _ => sum_le_sum fun l _ => hle m l) hpos.le

/-- The decoder of the eavesdropper in the bin of the message `m`. -/
def eveDec (D : (m : Fin M) → (Fin n → γ) → Fin L) (w : (Fin n → γ) × Fin M) : Fin L := D w.2 w.1

/-- The law of `((M, L), Zⁿ)` for a codebook. -/
def wtBinLaw (V : 𝒰 → γ → ℝ) (C : Fin (M * L) → Fin n → 𝒰) : (Fin M × Fin L) × (Fin n → γ) → ℝ :=
  jointOf (uniformPMF _) fun z => channelExt V n (C (binIdx M L z.1 z.2))

omit [Fintype 𝒰] in
/-- **Pages 23-16 and 23-17 of [elgamal2010].** The information leakage: `I(M; Zⁿ) ≤ I(L; Zⁿ) -
log L + H(L | Zⁿ, M)`, and then Fano's inequality for the decoder of the eavesdropper. -/
lemma mutualInfo_wtBinLaw_le {V : 𝒰 → γ → ℝ} (hV : IsChannel V) (C : Fin (M * L) → Fin n → 𝒰)
    (D : (m : Fin M) → (Fin n → γ) → Fin L) :
    I[fun z => z.1.1 : Prod.snd ; wtBinLaw V C] ≤ codebookInfo V C - log L + log 2 +
      ((1 / M) * ∑ m, (ChannelCode.mk (fun l => C (binIdx M L m l)) (D m)).avgErrProb V) *
        log L := by
  classical
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hne : Nonempty (Fin M × Fin L) := ⟨(0, 0)⟩
  have hu : IsPMF (uniformPMF (Fin M × Fin L)) := uniformPMF_isPMF
  have hT : IsChannel fun z : Fin M × Fin L => channelExt V n (C (binIdx M L z.1 z.2)) :=
    fun z => hV.ext n _
  have hμ : IsPMF (wtBinLaw V C) := jointOf_isPMF hu hT
  set M' : (Fin M × Fin L) × (Fin n → γ) → Fin M := fun z => z.1.1
  set L' : (Fin M × Fin L) × (Fin n → γ) → Fin L := fun z => z.1.2
  have hdist : dist (wtBinLaw V C) Prod.fst = uniformPMF (Fin M × Fin L) := dist_jointOf_fst hT
  -- `I(M, L; Zⁿ)` is the information of the codebook.
  have hinfo : I[Prod.fst : Prod.snd ; wtBinLaw V C] = codebookInfo V C := by
    have h₁ := mutualInfoOf_eq hu hT
    rw [mutualInfoOf] at h₁
    change I[Prod.fst : Prod.snd ; wtBinLaw V C] = _ at h₁
    rw [h₁, codebookInfo]
    congr 1
    · congr 1
      funext z
      simp only [outDist, codebookOut, uniformPMF, Fintype.card_prod, Fintype.card_fin]
      rw [← finProdFinEquiv.sum_comp, mul_sum]
      simp only [binIdx]
    · simp only [uniformPMF, Fintype.card_prod, Fintype.card_fin]
      rw [← finProdFinEquiv.sum_comp, mul_sum]
      simp only [binIdx]
  -- The chain rule.
  have h₁ := chain_rule_mutualInfo₂ hμ Prod.snd L' M'
  have h₂ : I[Prod.snd : pair L' M' ; wtBinLaw V C] = I[Prod.fst : Prod.snd ; wtBinLaw V C] := by
    rw [mutualInfo_comm hμ]
    have e := mutualInfo_congr_right (μ := wtBinLaw V C) hμ (Prod.snd)
      (Y := (Prod.fst : (Fin M × Fin L) × (Fin n → γ) → _)) (Y' := pair L' M') Prod.swap
      Prod.swap_injective fun _ => rfl
    rw [mutualInfo_comm hμ, e, mutualInfo_comm hμ]
  have h₃ : I[Prod.snd : L' | M' ; wtBinLaw V C] = H[L' | M' ; wtBinLaw V C] -
      H[L' | pair Prod.snd M' ; wtBinLaw V C] := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
  -- `H(L | M) = log L`.
  have h₄ : H[L' | M' ; wtBinLaw V C] = log L := by
    rw [condEntropy_eq_sub hμ]
    have e₁ : H[pair M' L' ; wtBinLaw V C] = log M + log L := by
      have : pair M' L' = Prod.fst := rfl
      rw [this, entropyRV, hdist, entropy_uniformPMF, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin]
      push_cast
      rw [log_mul hMpos.ne' hLpos.ne']
    have e₂ : H[M' ; wtBinLaw V C] = log M := by
      have h := dist_comp_eq (wtBinLaw V C) Prod.fst (Prod.fst : Fin M × Fin L → _)
      rw [hdist] at h
      have h' : dist (uniformPMF (Fin M × Fin L)) Prod.fst = uniformPMF (Fin M) := by
        funext m
        rw [dist_fst]
        simp only [uniformPMF, Fintype.card_prod, Fintype.card_fin, sum_const, card_univ,
          nsmul_eq_mul]
        push_cast
        field_simp
      rw [h'] at h
      have hM' : H[M' ; wtBinLaw V C] = entropy (uniformPMF (Fin M)) := by
        rw [entropyRV, ← h]
        rfl
      rw [hM', entropy_uniformPMF, Fintype.card_fin]
    linarith
  -- Fano's inequality.
  have hF := fano_weak hμ L' (pair Prod.snd M') (eveDec D)
  rw [Fintype.card_fin] at hF
  have herr : InfoTheory.errProb (wtBinLaw V C) L' (pair Prod.snd M') (eveDec D) =
      (1 / M) * ∑ m, (ChannelCode.mk (fun l => C (binIdx M L m l)) (D m)).avgErrProb V := by
    simp only [InfoTheory.errProb, ChannelCode.avgErrProb, ChannelCode.condErrProb, wtBinLaw,
      jointOf, uniformPMF, Fintype.card_prod, Fintype.card_fin, eveDec, pair, L', M',
      Fintype.sum_prod_type]
    rw [mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [sum_div, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [sum_div, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    by_cases h : D m z = l
    · simp [h]
    · simp only [h, ne_eq, not_false_eq_true, ite_true]
      push_cast
      field_simp
  rw [herr] at hF
  have hfinal : I[M' : Prod.snd ; wtBinLaw V C] = I[Prod.snd : M' ; wtBinLaw V C] :=
    mutualInfo_comm hμ _ _
  change I[M' : Prod.snd ; wtBinLaw V C] ≤ _
  rw [hfinal]
  rw [h₂, hinfo] at h₁
  linarith

omit [Fintype 𝒰] in
/-- The leakage of the code is the mutual information for the law of the codebook. -/
lemma leakage_wiretapCodeOf [Finite 𝒰] :
    (wiretapCodeOf hr C d).leakage W =
      I[fun z => z.1.1 : Prod.snd ; wtBinLaw (throughKernel r (bcMarg₂ W)) C] := by
  have := Fintype.ofFinite 𝒰
  classical
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine mutualInfo_eq_of_dist_pair_eq ?_
  funext ⟨m, z⟩
  rw [dist_wiretapCodeOf_Z]
  simp only [dist, pair, Prod.mk.injEq, wtBinLaw, jointOf, uniformPMF, Fintype.card_prod,
    Fintype.card_fin]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    sum_eq_single m (fun b _ hb => by simp [hb]) (by simp), mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_eq_single z (fun b _ hb => by simp [hb]) (by simp)]
  simp only [and_self, ite_true]
  push_cast
  rfl

end Code

/-! ### One code from a random codebook -/

section Random

variable {α β γ 𝒰 : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype 𝒰] {M L n : ℕ}
  {W : α → β × γ → ℝ} {r : 𝒰 → α → ℝ} {p : 𝒰 → ℝ}

/-- **Pages 23-14 to 23-17 of [elgamal2010], for one code.** For all `K ≥ 0` there are numbers
`G, P ≥ 0` and a code with `Pₑ ≤ P`, `I(M; Zⁿ) ≤ G - log L + log 2 + P log L` and
`G + K P ≤ n I(U; Z) + K (B₁ + B₂)`, where `B₁` and `B₂` are the bounds of the packing lemma for the
receiver and for the eavesdropper in a bin. -/
theorem exists_wiretap_code_le [NeZero M] [NeZero L] (hW : IsChannel W) (hp : IsPMF p)
    (hr : IsChannel r) (ε : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    ∃ (c : WiretapCode M n α β) (G P : ℝ), 0 ≤ G ∧ 0 ≤ P ∧ c.errProb W ≤ P ∧
      c.leakage W ≤ G - log L + log 2 + P * log L ∧
      G + K * P ≤ n * mutualInfoOf p (throughKernel r (bcMarg₂ W)) + K *
        (((1 - prob (jointIid (jointOf p (throughKernel r (bcMarg₁ W))) n)
            (jointTypicalSet (jointOf p (throughKernel r (bcMarg₁ W))) n ε)) +
          ((M * L : ℕ) - 1) * exp (-(n * (mutualInfoOf p (throughKernel r (bcMarg₁ W)) - 3 * ε)))) +
         ((1 - prob (jointIid (jointOf p (throughKernel r (bcMarg₂ W))) n)
            (jointTypicalSet (jointOf p (throughKernel r (bcMarg₂ W))) n ε)) +
          ((L : ℝ) - 1) * exp (-(n * (mutualInfoOf p (throughKernel r (bcMarg₂ W)) - 3 * ε))))) :=
            by
  classical
  set V₁ := throughKernel r (bcMarg₁ W) with hV₁d
  set V₂ := throughKernel r (bcMarg₂ W) with hV₂d
  have hV₁ : IsChannel V₁ := hr.throughKernel hW.bcMarg₁
  have hV₂ : IsChannel V₂ := hr.throughKernel hW.bcMarg₂
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hML : 0 < M * L := Nat.mul_pos hMpos hLpos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  set w₀ : Fin (M * L) := ⟨0, hML⟩
  set l₀ : Fin L := ⟨0, hLpos⟩
  set A₁ := jointTypicalSet (jointOf p V₁) n ε
  set A₂ := jointTypicalSet (jointOf p V₂) n ε
  set B₁ := (1 - prob (jointIid (jointOf p V₁) n) A₁) +
    ((M * L : ℕ) - 1) * exp (-(n * (mutualInfoOf p V₁ - 3 * ε)))
  set B₂ := (1 - prob (jointIid (jointOf p V₂) n) A₂) +
    ((L : ℝ) - 1) * exp (-(n * (mutualInfoOf p V₂ - 3 * ε)))
  have hpn := iidPMF_isPMF hp n
  have hlaw := iidPMF_isPMF hpn (M * L)
  -- The errors of the receiver and of the eavesdropper.
  set PB : (Fin (M * L) → Fin n → 𝒰) → ℝ := fun C => (typicalCode A₁ C w₀).avgErrProb V₁ with hPB
  set DE : (Fin (M * L) → Fin n → 𝒰) → (m : Fin M) → (Fin n → γ) → Fin L :=
    fun C m => typicalDecode A₂ (fun l => C (binIdx M L m l)) l₀ with hDE
  set PE : (Fin (M * L) → Fin n → 𝒰) → ℝ := fun C => (1 / M) *
    ∑ m, (ChannelCode.mk (fun l => C (binIdx M L m l)) (DE C m)).avgErrProb V₂ with hPE
  have havgB : ∑ C, iidPMF (iidPMF p n) (M * L) C * PB C ≤ B₁ :=
    sum_codebook_avgErr_le hp hV₁ ε w₀
  have havgE : ∑ C, iidPMF (iidPMF p n) (M * L) C * PE C ≤ B₂ := by
    have hm : ∀ m : Fin M, ∑ C, iidPMF (iidPMF p n) (M * L) C *
        (ChannelCode.mk (fun l => C (binIdx M L m l)) (DE C m)).avgErrProb V₂ ≤ B₂ := fun m => by
      have h := sum_iidPMF_comp_injective hpn (binIdx M L m) (binIdx_injective M L m)
        fun D : Fin L → Fin n → 𝒰 => (typicalCode A₂ D l₀).avgErrProb V₂
      exact (le_of_eq h).trans (sum_codebook_avgErr_le hp hV₂ ε l₀)
    simp only [hPE, mul_sum]
    rw [sum_comm]
    have hm' : ∀ m : Fin M, ∑ C, iidPMF (iidPMF p n) (M * L) C * (1 / (M : ℝ) *
        (ChannelCode.mk (fun l => C (binIdx M L m l)) (DE C m)).avgErrProb V₂) ≤ 1 / M * B₂ :=
      fun m => by
        have := mul_le_mul_of_nonneg_left (hm m) (by positivity : (0 : ℝ) ≤ 1 / M)
        rw [mul_sum] at this
        refine le_trans (le_of_eq (sum_congr rfl fun C _ => ?_)) this
        ring
    refine (sum_le_sum fun m _ => hm' m).trans (le_of_eq ?_)
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hG := sum_codebook_codebookInfo_le (n := n) hp hV₂ hML
  -- Choose the codebook.
  have havg : ∑ C, iidPMF (iidPMF p n) (M * L) C * (codebookInfo V₂ C + K * (PB C + PE C)) ≤
      n * mutualInfoOf p V₂ + K * (B₁ + B₂) := by
    simp only [mul_add]
    rw [sum_add_distrib]
    refine add_le_add hG ?_
    have : ∑ C, (iidPMF (iidPMF p n) (M * L) C * (K * PB C) +
        iidPMF (iidPMF p n) (M * L) C * (K * PE C)) =
        K * (∑ C, iidPMF (iidPMF p n) (M * L) C * PB C) +
          K * ∑ C, iidPMF (iidPMF p n) (M * L) C * PE C := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun C _ => by ring
    rw [this]
    exact add_le_add (mul_le_mul_of_nonneg_left havgB hK) (mul_le_mul_of_nonneg_left havgE hK)
  obtain ⟨C, hC⟩ := exists_le_of_sum_mul_le hlaw havg
  -- The bounds for this codebook.
  set c := wiretapCodeOf (α := α) (β := β) hr C (typicalDecode A₁ C w₀) with hc
  have hP₁ : 0 ≤ PB C := by
    simp only [hPB, ChannelCode.avgErrProb]
    refine div_nonneg (sum_nonneg fun i _ => ?_) (Nat.cast_nonneg _)
    exact sum_nonneg fun y _ => by
      split_ifs
      exacts [channelExt_nonneg hV₁ _ _, le_rfl]
  have hP₂ : 0 ≤ PE C := by
    simp only [hPE]
    refine mul_nonneg (by positivity) (sum_nonneg fun m _ => ?_)
    simp only [ChannelCode.avgErrProb]
    refine div_nonneg (sum_nonneg fun i _ => ?_) (Nat.cast_nonneg _)
    exact sum_nonneg fun y _ => by
      split_ifs
      exacts [channelExt_nonneg hV₂ _ _, le_rfl]
  have hG0 : 0 ≤ codebookInfo V₂ C := by
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
    have hne : Nonempty (Fin M × Fin L) := ⟨(⟨0, hMpos⟩, l₀)⟩
    have hT : IsChannel fun z : Fin (M * L) => channelExt V₂ n (C z) := fun z => hV₂.ext n _
    have hne' : Nonempty (Fin (M * L)) := ⟨w₀⟩
    have h := mutualInfoOf_nonneg (uniformPMF_isPMF (α := Fin (M * L))) hT
    rw [mutualInfoOf_eq uniformPMF_isPMF hT] at h
    have e₁ : outDist (uniformPMF (Fin (M * L))) (fun z => channelExt V₂ n (C z)) =
        codebookOut V₂ C := by
      funext z
      simp only [outDist, codebookOut, uniformPMF, Fintype.card_fin, mul_sum]
    have e₂ : ∑ x, uniformPMF (Fin (M * L)) x * entropy (channelExt V₂ n (C x)) =
        (1 / ((M * L : ℕ) : ℝ)) * ∑ w, entropy (channelExt V₂ n (C w)) := by
      simp only [uniformPMF, Fintype.card_fin, mul_sum]
    rw [e₁, e₂] at h
    exact h
  have herr := errProb_wiretapCodeOf_le (W := W) hr C (typicalDecode A₁ C w₀) hV₁
  have hleak := mutualInfo_wtBinLaw_le hV₂ C (DE C)
  rw [← leakage_wiretapCodeOf (W := W) hr C (typicalDecode A₁ C w₀)] at hleak
  have hlogL : 0 ≤ log L := log_natCast_nonneg _
  refine ⟨c, codebookInfo V₂ C, PB C + PE C, hG0, add_nonneg hP₁ hP₂, ?_, ?_, hC⟩
  · have : (ChannelCode.mk C (typicalDecode A₁ C w₀)).avgErrProb V₁ = PB C := rfl
    rw [this] at herr
    linarith
  · have h₁ : PE C * log L ≤ (PB C + PE C) * log L :=
      mul_le_mul_of_nonneg_right (by linarith) hlogL
    linarith

end Random

/-! ### Theorem 3 -/

section Theorem

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] {W : α → β × γ → ℝ}

/-- The bound of the packing lemma for the receiver. -/
lemma wiretap_packing₁ {M L n : ℕ} {a ρ I₁ δ : ℝ} (hδ : 0 ≤ δ) (hM : 0 < M) (hL : 0 < L)
    (hlogM : log M ≤ n * a + log 2) (hlogL : log L ≤ n * ρ) (h : a + ρ ≤ I₁ - 4 * δ) :
    ((M * L : ℕ) - 1 : ℝ) * exp (-(n * (I₁ - 3 * (δ / 3)))) ≤ 2 * exp (-(n * δ)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hle : ((M * L : ℕ) : ℝ) ≤ 2 * exp (n * (a + ρ)) := by
    push_cast
    have hMe : (M : ℝ) ≤ exp (n * a + log 2) := by
      rw [← exp_log hMpos]
      exact exp_le_exp.2 hlogM
    have hLe : (L : ℝ) ≤ exp (n * ρ) := by
      rw [← exp_log hLpos]
      exact exp_le_exp.2 hlogL
    calc (M : ℝ) * L ≤ exp (n * a + log 2) * exp (n * ρ) :=
          mul_le_mul hMe hLe hLpos.le (exp_pos _).le
      _ = _ := by
          rw [← exp_add, show n * a + log 2 + n * ρ = log 2 + n * (a + ρ) by ring, exp_add,
            exp_log two_pos]
  have h₁ : ((M * L : ℕ) - 1 : ℝ) ≤ 2 * exp (n * (a + ρ)) := by linarith
  calc ((M * L : ℕ) - 1 : ℝ) * exp (-(n * (I₁ - 3 * (δ / 3))))
      ≤ 2 * exp (n * (a + ρ)) * exp (-(n * (I₁ - 3 * (δ / 3)))) :=
        mul_le_mul_of_nonneg_right h₁ (exp_pos _).le
    _ = 2 * exp (n * (a + ρ) + -(n * (I₁ - 3 * (δ / 3)))) := by
        rw [mul_assoc, ← exp_add]
    _ ≤ 2 * exp (-(n * δ)) := by
        refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num)
        have h₂ : (n : ℝ) * (a + ρ) ≤ n * (I₁ - 4 * δ) := mul_le_mul_of_nonneg_left h hn0
        have h₃ : (n : ℝ) * (I₁ - 3 * (δ / 3)) = n * (I₁ - 4 * δ) + n * (3 * δ) := by ring
        have h₄ : (n : ℝ) * (3 * δ) = n * δ + n * (2 * δ) := by ring
        have h₅ : 0 ≤ (n : ℝ) * (2 * δ) := by positivity
        linarith

/-- The bound of the packing lemma for the eavesdropper in a bin. -/
lemma wiretap_packing₂ {L n : ℕ} {I₂ δ ρ : ℝ} (hL : 0 < L) (hlogL : log L ≤ n * ρ)
    (h : L = 1 ∨ ρ = I₂ - 2 * δ) :
    ((L : ℝ) - 1) * exp (-(n * (I₂ - 3 * (δ / 3)))) ≤ exp (-(n * δ)) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rcases h with h | h
  · simp [h, (exp_pos _).le]
  · have hLe : (L : ℝ) ≤ exp (n * ρ) := by
      rw [← exp_log hLpos]
      exact exp_le_exp.2 hlogL
    calc ((L : ℝ) - 1) * exp (-(n * (I₂ - 3 * (δ / 3))))
        ≤ exp (n * ρ) * exp (-(n * (I₂ - 3 * (δ / 3)))) :=
          mul_le_mul_of_nonneg_right (by linarith) (exp_pos _).le
      _ = exp (-(n * δ)) := by
          rw [← exp_add, h]
          congr 1
          ring

/-- The arithmetic of the end of the proof of achievability. -/
lemma wiretap_conclude {N K₀ η δ ε I₂ ρ B G P E LL logL l₂ : ℝ} (hN : 0 < N) (hK₀ : 0 < K₀)
    (hK₀η : K₀ * η = I₂ + 1) (hη₁ : η ≤ ε / 2) (hη₂ : 2 * η * I₂ ≤ ε / 8) (hδ₂ : 8 * δ ≤ ε)
    (hδ0 : 0 < δ) (hη0 : 0 < η) (hρ₁ : I₂ - 2 * δ ≤ ρ) (hρ₂ : ρ ≤ I₂) (hG0 : 0 ≤ G)
    (hP0 : 0 ≤ P) (herr : E ≤ P) (hleak : LL ≤ G - logL + l₂ + P * logL)
    (hF : G + N * K₀ * P ≤ N * I₂ + N * K₀ * B) (hBη : B ≤ η) (hBK : K₀ * B ≤ δ)
    (hlogL₀ : 0 ≤ logL) (hlogL₁ : logL ≤ N * ρ) (hlogL₂ : N * ρ - l₂ ≤ logL)
    (hnε : 2 * l₂ ≤ N * (ε / 8)) : E ≤ ε ∧ LL ≤ N * ε := by
  have h₀ : N * K₀ * B = N * (K₀ * B) := by ring
  have h₁ : N * (K₀ * B) ≤ N * δ := mul_le_mul_of_nonneg_left hBK hN.le
  have h₂ : 0 ≤ N * K₀ * P := by positivity
  have hGbd : G ≤ N * I₂ + N * δ := by linarith
  have hPbd : P ≤ 2 * η := by
    have h₃ : N * (K₀ * P) ≤ N * (I₂ + K₀ * B) := by
      have e₁ : N * (K₀ * P) = N * K₀ * P := by ring
      have e₂ : N * (I₂ + K₀ * B) = N * I₂ + N * K₀ * B := by ring
      rw [e₁, e₂]
      linarith
    have h₄ : K₀ * P ≤ I₂ + K₀ * B := le_of_mul_le_mul_left h₃ hN
    have h₅ : K₀ * B ≤ K₀ * η := mul_le_mul_of_nonneg_left hBη hK₀.le
    have h₆ : K₀ * P ≤ K₀ * (2 * η) := by
      have e : K₀ * (2 * η) = 2 * (K₀ * η) := by ring
      rw [e]
      linarith
    exact le_of_mul_le_mul_left h₆ hK₀
  refine ⟨by linarith, ?_⟩
  have hlogI : logL ≤ N * I₂ := hlogL₁.trans (mul_le_mul_of_nonneg_left hρ₂ hN.le)
  have h₃ : P * logL ≤ 2 * η * (N * I₂) := mul_le_mul hPbd hlogI hlogL₀ (by positivity)
  have h₄ : 2 * η * (N * I₂) ≤ N * (ε / 8) := by
    have := mul_le_mul_of_nonneg_left hη₂ hN.le
    have e : N * (2 * η * I₂) = 2 * η * (N * I₂) := by ring
    linarith
  have h₅ : N * (I₂ - ρ) ≤ N * (2 * δ) := mul_le_mul_of_nonneg_left (by linarith) hN.le
  have h₆ : N * (3 * δ) ≤ N * (3 * ε / 8) := mul_le_mul_of_nonneg_left (by linarith) hN.le
  have e₁ : N * (I₂ - ρ) = N * I₂ - N * ρ := by ring
  have e₂ : N * (2 * δ) + N * δ = N * (3 * δ) := by ring
  have e₃ : N * (ε / 8) + N * (3 * ε / 8) + N * (ε / 8) + N * (3 * ε / 8) = N * ε := by ring
  have h₇ : 0 ≤ N * (3 * ε / 8) := mul_nonneg hN.le (by linarith)
  linarith

/-- **Pages 23-14 to 23-17 of [elgamal2010]: achievability**, for a law given by `p(u)` and
`p(x | u)`, with a fixed `ε`. -/
lemma exists_wiretap_code_of_lt {𝒰 : Type*} [Fintype 𝒰] (hW : IsChannel W) {p : 𝒰 → ℝ}
    (hpP : IsPMF p) {r : 𝒰 → α → ℝ} (hr : IsChannel r) {R : ℝ} (hR : 0 ≤ R)
    (hlt : R * log 2 < mutualInfoOf p (throughKernel r (bcMarg₁ W)) -
      mutualInfoOf p (throughKernel r (bcMarg₂ W))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ c : WiretapCode (2 ^ ⌈n * R⌉₊) n α β,
      c.errProb W ≤ ε ∧ c.leakage W ≤ n * ε := by
  have hl := log_pos one_lt_two
  set V₁ := throughKernel r (bcMarg₁ W) with hV₁d
  set V₂ := throughKernel r (bcMarg₂ W) with hV₂d
  have hV₁ : IsChannel V₁ := hr.throughKernel hW.bcMarg₁
  have hV₂ : IsChannel V₂ := hr.throughKernel hW.bcMarg₂
  set I₁ := mutualInfoOf p V₁ with hI₁
  set I₂ := mutualInfoOf p V₂ with hI₂
  have hI₂0 : 0 ≤ I₂ := mutualInfoOf_nonneg hpP hV₂
  -- The parameters.
  set δ := min ((I₁ - I₂ - R * log 2) / 8) (ε / 8) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ₁ : 8 * δ ≤ I₁ - I₂ - R * log 2 := by
    have := min_le_left ((I₁ - I₂ - R * log 2) / 8) (ε / 8)
    linarith
  have hδ₂ : 8 * δ ≤ ε := by
    have := min_le_right ((I₁ - I₂ - R * log 2) / 8) (ε / 8)
    linarith
  set ρ := max 0 (I₂ - 2 * δ) with hρ
  have hρ0 : 0 ≤ ρ := le_max_left _ _
  have hρ₁ : I₂ - 2 * δ ≤ ρ := le_max_right _ _
  have hρ₂ : ρ ≤ I₂ := max_le hI₂0 (by linarith)
  have hρ₃ : R * log 2 + ρ ≤ I₁ - 4 * δ := by
    rcases max_cases 0 (I₂ - 2 * δ) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hρ, h] <;> linarith
  set s := ρ / log 2 with hs
  have hs0 : 0 ≤ s := div_nonneg hρ0 hl.le
  have hsρ : s * log 2 = ρ := div_mul_cancel₀ ρ hl.ne'
  set η := min (ε / 2) (ε / (16 * (I₂ + 1))) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by positivity)
  have hη₁ : η ≤ ε / 2 := min_le_left _ _
  have hη₂ : 2 * η * I₂ ≤ ε / 8 := by
    have h₁ : η ≤ ε / (16 * (I₂ + 1)) := min_le_right _ _
    have h₂ : η * (16 * (I₂ + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 h₁
    nlinarith
  set K₀ := (I₂ + 1) / η with hK₀
  have hK₀0 : 0 < K₀ := by positivity
  have hK₀η : K₀ * η = I₂ + 1 := div_mul_cancel₀ _ hη0.ne'
  -- The bounds of the packing lemma tend to `0`.
  set Bd : ℕ → ℝ := fun n =>
    ((1 - prob (jointIid (jointOf p V₁) n) (jointTypicalSet (jointOf p V₁) n (δ / 3))) +
        2 * exp (-(n * δ))) +
      ((1 - prob (jointIid (jointOf p V₂) n) (jointTypicalSet (jointOf p V₂) n (δ / 3))) +
        exp (-(n * δ))) with hBd
  have hBdlim : Tendsto Bd atTop (𝓝 0) := by
    have hδ3 : 0 < δ / 3 := by positivity
    have t₁ : Tendsto (fun n => 1 - prob (jointIid (jointOf p V₁) n)
        (jointTypicalSet (jointOf p V₁) n (δ / 3))) atTop (𝓝 0) := by
      simpa using (tendsto_prob_jointTypicalSet (jointOf_isPMF hpP hV₁) hδ3).const_sub 1
    have t₂ : Tendsto (fun n => 1 - prob (jointIid (jointOf p V₂) n)
        (jointTypicalSet (jointOf p V₂) n (δ / 3))) atTop (𝓝 0) := by
      simpa using (tendsto_prob_jointTypicalSet (jointOf_isPMF hpP hV₂) hδ3).const_sub 1
    have t₃ := tendsto_exp_neg_mul_nat hδ0
    simpa [hBd] using (t₁.add (t₃.const_mul 2)).add (t₂.add t₃)
  have hthr : 0 < min η (δ / K₀) := lt_min hη0 (by positivity)
  filter_upwards [(tendsto_order.1 hBdlim).2 _ hthr,
    eventually_gt_atTop ⌈16 * log 2 / ε⌉₊] with n hn hn1
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hnε : 2 * log 2 ≤ n * (ε / 8) := by
    have h₁ : 16 * log 2 / ε < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
    rw [div_lt_iff₀ hε] at h₁
    linarith
  have hMp : 0 < 2 ^ ⌈n * R⌉₊ := by positivity
  have hLp : 0 < 2 ^ ⌊n * s⌋₊ := by positivity
  have : NeZero (2 ^ ⌈n * R⌉₊) := ⟨hMp.ne'⟩
  have : NeZero (2 ^ ⌊n * s⌋₊) := ⟨hLp.ne'⟩
  have hLpos : (0 : ℝ) < (2 ^ ⌊n * s⌋₊ : ℕ) := by exact_mod_cast hLp
  have hlogL₁ : log (2 ^ ⌊n * s⌋₊ : ℕ) ≤ n * ρ := by
    have := log_two_pow_floor_le n hs0
    rwa [hsρ] at this
  have hlogL₂ : n * ρ - log 2 ≤ log (2 ^ ⌊n * s⌋₊ : ℕ) := by
    have h₁ := exp_le_two_pow_floor n s
    rw [hsρ] at h₁
    rw [le_log_iff_exp_le hLpos]
    exact h₁
  have hlogM := log_two_pow_ceil_le n hR
  -- The code.
  obtain ⟨c, G, P, hG0, hP0, herr, hleak, hF⟩ :=
    exists_wiretap_code_le (M := 2 ^ ⌈n * R⌉₊) (L := 2 ^ ⌊n * s⌋₊) (n := n) hW hpP hr (δ / 3)
      (K := n * K₀) (by positivity)
  have hb₁ := wiretap_packing₁ (I₁ := I₁) hδ0.le hMp hLp hlogM hlogL₁ hρ₃
  have hb₂ : (((2 ^ ⌊n * s⌋₊ : ℕ) : ℝ) - 1) * exp (-(n * (I₂ - 3 * (δ / 3)))) ≤ exp (-(n * δ)) := by
    refine wiretap_packing₂ hLp hlogL₁ ?_
    rcases max_cases 0 (I₂ - 2 * δ) with ⟨h, -⟩ | ⟨h, -⟩
    · left
      have : s = 0 := by rw [hs, hρ, h, zero_div]
      simp [this]
    · right
      rw [hρ, h]
  have hB : ((1 - prob (jointIid (jointOf p V₁) n) (jointTypicalSet (jointOf p V₁) n (δ / 3))) +
      (((2 ^ ⌈n * R⌉₊ * 2 ^ ⌊n * s⌋₊ : ℕ) : ℝ) - 1) * exp (-(n * (I₁ - 3 * (δ / 3))))) +
      ((1 - prob (jointIid (jointOf p V₂) n) (jointTypicalSet (jointOf p V₂) n (δ / 3))) +
      (((2 ^ ⌊n * s⌋₊ : ℕ) : ℝ) - 1) * exp (-(n * (I₂ - 3 * (δ / 3))))) ≤ Bd n := by
    simp only [hBd]
    linarith
  have hF₂ := hF.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hB (by positivity)))
  have hBη : Bd n ≤ η := (hn.trans_le (min_le_left _ _)).le
  have hBK : K₀ * Bd n ≤ δ := by
    have := (lt_div_iff₀ hK₀0).1 (hn.trans_le (min_le_right _ _))
    linarith
  exact ⟨c, wiretap_conclude hn0 hK₀0 hK₀η hη₁ hη₂ hδ₂ hδ0 hη0 hρ₁ hρ₂ hG0 hP0 herr hleak hF₂
    hBη hBK (log_natCast_nonneg _) hlogL₁ hlogL₂ hnε⟩

/-- **Pages 23-14 to 23-17 of [elgamal2010]: achievability.** Every rate below the gap of a law
`p(u, x)` is achievable. -/
theorem isAchievableWiretap_of_lt {𝒰 : Type*} [Fintype 𝒰] (hW : IsChannel W) {q : 𝒰 × α → ℝ}
    (hq : IsPMF q) {R : ℝ} (hR : 0 ≤ R) (hlt : R * log 2 < wiretapGap q W) :
    IsAchievableWiretap W R := by
  have hq' : (fun z : 𝒰 × α => (∑ x, q (z.1, x)) * wtPosterior q z.1 z.2) = q :=
    funext (marg_mul_wtPosterior hq)
  have e₁ : bcInfoUY₁ q W = mutualInfoOf (fun u => ∑ x, q (u, x))
      (throughKernel (wtPosterior q) (bcMarg₁ W)) := by
    conv_lhs => rw [← hq']
    exact bcInfoUY₁_kernel (fun u => ∑ x, q (u, x)) (wtPosterior q) W
  have e₂ : bcInfoUY₂ q W = mutualInfoOf (fun u => ∑ x, q (u, x))
      (throughKernel (wtPosterior q) (bcMarg₂ W)) := by
    conv_lhs => rw [← hq']
    exact bcInfoUY₂_kernel (fun u => ∑ x, q (u, x)) (wtPosterior q) W
  have hgap : wiretapGap q W = mutualInfoOf (fun u => ∑ x, q (u, x))
      (throughKernel (wtPosterior q) (bcMarg₁ W)) - mutualInfoOf (fun u => ∑ x, q (u, x))
      (throughKernel (wtPosterior q) (bcMarg₂ W)) := by
    rw [wiretapGap, e₁, e₂]
  rw [hgap] at hlt
  exact ⟨hR, fun ε hε => exists_wiretap_code_of_lt hW (wiretapMarg_isPMF hq)
    (wtPosterior_isChannel hq) hR hlt hε⟩

/-- **Theorem 3 of Lecture 23 of [elgamal2010], page 23-9.** The secrecy capacity of the DM-WTC is
`C_S = max_{p(u, x)} (I(U; Y) - I(U; Z))`, with `|𝒰| ≤ |𝒳|`, in bits. -/
theorem wiretapCapacity_eq [Nonempty α] (hW : IsChannel W) :
    wiretapCapacity W = wiretapValue W / log 2 := by
  have hl := log_pos one_lt_two
  have hV := wiretapValue_nonneg hW
  have hup : ∀ R ∈ {R | IsAchievableWiretap W R}, R ≤ wiretapValue W / log 2 := fun R hR =>
    (le_div_iff₀ hl).2 (IsAchievableWiretap.le hW hR)
  refine le_antisymm (Real.sSup_le hup (div_nonneg hV hl.le)) ?_
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  rcases lt_or_ge r 0 with h0 | h0
  · exact h0.le.trans (Real.sSup_nonneg fun R hR => hR.1)
  · obtain ⟨q, hq, hqV⟩ := exists_wiretapValue_eq hW
    have hmem : r ∈ {R | IsAchievableWiretap W R} :=
      isAchievableWiretap_of_lt hW hq h0 (by
        rw [hqV]
        exact (lt_div_iff₀ hl).1 hr)
    exact le_csSup ⟨_, hup⟩ hmem

end Theorem

end InfoTheory
