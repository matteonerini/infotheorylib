/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MDCovering

/-!
# The Zhang–Berger inner bound

This file proves the Zhang–Berger inner bound for the multiple description problem, Theorem 4 of
Lecture 14 of El Gamal and Kim. A rate pair `(R₁, R₂)` is achievable if
`R₁ > I(X; X̂₁, U)`, `R₂ > I(X; X̂₂, U)` and
`R₁ + R₂ > I(X; X̂₀, X̂₁, X̂₂ | U) + 2 I(U; X) + I(X̂₁; X̂₂ | U)`.

The El Gamal–Cover inner bound, Theorem 1 of the notes, is the special case where `U` is the time
sharing variable `Q`, independent of `X`, see `InfoTheoryLib.Network.MDCases`.

## Main statements

* `exists_zb_chain`: the choice of the three layers of codebooks.
* `isAchievableMD_of_split`: the coding theorem for the rates of the layers.
* `isAchievableMD_zhangBerger`: **the Zhang–Berger inner bound**.

## Implementation notes

The random variables live on a finite probability space `(Ω, μ)`, so that no conditional pmf has to
be written in the statements. The source is `X`, and the source law is `dist μ X`. The layers are
chosen one at a time with `exists_layer`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 14
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α υ β₀ β₁ β₂ : Type*} [Fintype Ω] [Fintype α] [Fintype υ] [Fintype β₀] [Fintype β₁]
  [Fintype β₂] {μ : Ω → ℝ} {X : Ω → α} {U : Ω → υ} {Y₀ : Ω → β₀} {Y₁ : Ω → β₁} {Y₂ : Ω → β₂}

/-! ### The three layers -/

section Chain

variable {n L₀ L₁ L₂ L₃ : ℕ} {ε₀ ε₁ ε₂ ε₃ η₀ η₁ η₂ : ℝ}

omit [Fintype α] in
/-- Replace an `if` by an equivalent one, whatever the decidability instances are. -/
lemma mul_ite_congr {p q : Prop} {dp : Decidable p} {dq : Decidable q} (a u v : ℝ) (h : p ↔ q) :
    a * (if p then u else v) = a * (if q then u else v) := by
  by_cases hp : p
  · simp [hp, h.1 hp]
  · have hq : ¬ q := fun hq => hp (h.2 hq)
    simp [hp, hq]

/-- The sequence of all the random variables: `((((U, (X̂₁, X̂₂)), X), X̂₀)`. -/
def zbSeq (u : Fin n → υ) (c₁ : Fin n → β₁) (c₂ : Fin n → β₂) (x : Fin n → α) (c₀ : Fin n → β₀) :
    Fin n → ((υ × β₁ × β₂) × α) × β₀ :=
  zipSeq (zipSeq (zipSeq u (zipSeq c₁ c₂)) x) c₀

open Classical in
/-- **Three layers of a superposition code.** The abstract form of the choice of the codebooks:
the laws and the relations of a layer may depend on the codebooks of the previous layers. -/
theorem exists_three_layers {A 𝒟₀ 𝒟₁ 𝒟₂ J₀ J₁ J₂ : Type*} [Fintype A] [Fintype 𝒟₀] [Fintype 𝒟₁]
    [Fintype 𝒟₂] [Fintype J₀] [Fintype J₁] [Nonempty 𝒟₀] [Nonempty 𝒟₁] [Nonempty 𝒟₂] [Nonempty J₀]
    [Nonempty J₁] [Nonempty J₂] {w : A → ℝ} (hw : IsPMF w) (G : A → Prop) (ν₀ : 𝒟₀ → ℝ)
    (R₀ : 𝒟₀ → A → J₀ → Prop) (ν₁ : 𝒟₀ → J₀ → 𝒟₁ → ℝ) (R₁ : 𝒟₀ → J₀ → 𝒟₁ → A → J₁ → Prop)
    (ν₂ : 𝒟₀ → (J₀ → 𝒟₁) → J₀ × J₁ → 𝒟₂ → ℝ)
    (R₂ : 𝒟₀ → (J₀ → 𝒟₁) → J₀ × J₁ → 𝒟₂ → A → J₂ → Prop)
    (hη₀ : 0 ≤ η₀) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (h₀ : ∀ x, G x → IsPMF ν₀ ∧ ∑ C, ν₀ C * (if ∀ j, ¬ R₀ C x j then 1 else 0) ≤ η₀)
    (h₁ : ∀ C x j, R₀ C x j → IsPMF (ν₁ C j) ∧
      ∑ D, ν₁ C j D * (if ∀ l, ¬ R₁ C j D x l then 1 else 0) ≤ η₁)
    (h₂ : ∀ C D x j l, R₁ C j (D j) x l → IsPMF (ν₂ C D (j, l)) ∧
      ∑ E, ν₂ C D (j, l) E * (if ∀ m, ¬ R₂ C D (j, l) E x m then 1 else 0) ≤ η₂) :
    ∃ (C : 𝒟₀) (D : J₀ → 𝒟₁) (E : J₀ × J₁ → 𝒟₂) (f₀ : A → J₀) (f₁ : A → J₁) (f₂ : A → J₂),
      ∑ x, w x * (if R₂ C D (f₀ x, f₁ x) (E (f₀ x, f₁ x)) x (f₂ x) then 0 else 1) ≤
        ∑ x, w x * (if G x then 0 else 1) + η₀ + η₁ + η₂ := by
  obtain ⟨C', f₀, hC⟩ := exists_layer hw (fun _ => ()) G (fun _ => ν₀) (fun _ C x j => R₀ C x j) hη₀
    fun x hx => ⟨(h₀ x hx).1, le_trans (le_of_eq (sum_congr rfl fun _ _ =>
      mul_ite_congr _ _ _ Iff.rfl)) (h₀ x hx).2⟩
  obtain ⟨D, f₁, hD⟩ := exists_layer hw f₀ (fun x => G x ∧ R₀ (C' ()) x (f₀ x)) (ν₁ (C' ()))
    (fun j D x l => R₁ (C' ()) j D x l) hη₁ fun x hx =>
      ⟨(h₁ _ x _ hx.2).1, le_trans (le_of_eq (sum_congr rfl fun _ _ =>
        mul_ite_congr _ _ _ Iff.rfl)) (h₁ _ x _ hx.2).2⟩
  obtain ⟨E, f₂, hE⟩ := exists_layer hw (fun x => (f₀ x, f₁ x))
    (fun x => (G x ∧ R₀ (C' ()) x (f₀ x)) ∧ R₁ (C' ()) (f₀ x) (D (f₀ x)) x (f₁ x))
    (ν₂ (C' ()) D) (fun i E x m => R₂ (C' ()) D i E x m) hη₂ fun x hx =>
      ⟨(h₂ _ D x _ _ hx.2).1, le_trans (le_of_eq (sum_congr rfl fun _ _ =>
        mul_ite_congr _ _ _ Iff.rfl)) (h₂ _ D x _ _ hx.2).2⟩
  refine ⟨C' (), D, E, f₀, f₁, f₂, ?_⟩
  have hsub : ∑ x, w x * (if R₂ (C' ()) D (f₀ x, f₁ x) (E (f₀ x, f₁ x)) x (f₂ x) then 0 else 1) ≤
      ∑ x, w x * (if ((G x ∧ R₀ (C' ()) x (f₀ x)) ∧ R₁ (C' ()) (f₀ x) (D (f₀ x)) x (f₁ x)) ∧
        R₂ (C' ()) D (f₀ x, f₁ x) (E (f₀ x, f₁ x)) x (f₂ x) then 0 else 1) := by
    refine sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hw.nonneg x)
    by_cases h : ((G x ∧ R₀ (C' ()) x (f₀ x)) ∧ R₁ (C' ()) (f₀ x) (D (f₀ x)) x (f₁ x)) ∧
        R₂ (C' ()) D (f₀ x, f₁ x) (E (f₀ x, f₁ x)) x (f₂ x)
    · have h2 := h.2
      rw [ite_eq_left h2, ite_eq_left h]
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  have e0 : ∑ x, w x * (if G x ∧ R₀ (C' ()) x (f₀ x) then 0 else 1) ≤
      ∑ x, w x * (if G x then 0 else 1) + η₀ := by
    convert hC
  have e1 : ∑ x, w x * (if (G x ∧ R₀ (C' ()) x (f₀ x)) ∧
      R₁ (C' ()) (f₀ x) (D (f₀ x)) x (f₁ x) then 0 else 1) ≤
      ∑ x, w x * (if G x ∧ R₀ (C' ()) x (f₀ x) then 0 else 1) + η₁ := by
    convert hD
  have e2 : ∑ x, w x * (if ((G x ∧ R₀ (C' ()) x (f₀ x)) ∧
      R₁ (C' ()) (f₀ x) (D (f₀ x)) x (f₁ x)) ∧
      R₂ (C' ()) D (f₀ x, f₁ x) (E (f₀ x, f₁ x)) x (f₂ x) then 0 else 1) ≤
      ∑ x, w x * (if (G x ∧ R₀ (C' ()) x (f₀ x)) ∧
        R₁ (C' ()) (f₀ x) (D (f₀ x)) x (f₁ x) then 0 else 1) + η₂ := by
    convert hE
  linarith

open Classical in
/-- **The choice of the codebooks.** If each of the three layers fails with probability at most
`ηⱼ` for a typical sequence, then there are codebooks and encoders such that the sequences are
jointly typical except with probability at most `P{Xⁿ ∉ T} + η₀ + η₁ + η₂`. -/
theorem exists_zb_chain (hμ : IsPMF μ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₃ : 0 < L₃)
    [Nonempty υ] [Nonempty β₀] [Nonempty β₁] [Nonempty β₂] (hη₀ : 0 ≤ η₀) (hη₁ : 0 ≤ η₁)
    (hη₂ : 0 ≤ η₂)
    (h₀ : ∀ x ∈ robustTypicalSet (dist μ X) n ε₀,
      ∑ C : Fin L₀ → Fin n → υ, iidPMF (iidPMF (dist μ U) n) L₀ C *
        (if ∀ m, ¬ zipSeq x (C m) ∈ robustTypicalSet (dist μ (pair X U)) n ε₁ then 1 else 0) ≤ η₀)
    (h₁ : ∀ (u : Fin n → υ) (x : Fin n → α),
      zipSeq u x ∈ robustTypicalSet (dist μ (pair U X)) n ε₁ →
      IsPMF (coverLaw (channelExt (condDist μ Y₁ U) n u) (channelExt (condDist μ Y₂ U) n u) L₁ L₂) ∧
      ∑ D, coverLaw (channelExt (condDist μ Y₁ U) n u) (channelExt (condDist μ Y₂ U) n u) L₁ L₂ D *
          (if ∀ l₁ l₂, ¬ zipSeq (zipSeq u (zipSeq x (D.1 l₁))) (D.2 l₂) ∈
            robustTypicalSet (triLaw μ U (pair X Y₁) Y₂) n ε₂ then 1 else 0) ≤ η₁)
    (h₂ : ∀ (v : Fin n → υ × β₁ × β₂) (x : Fin n → α),
      zipSeq v x ∈ robustTypicalSet (dist μ (pair (pair U (pair Y₁ Y₂)) X)) n ε₂ →
      IsPMF (iidPMF (channelExt (condDist μ Y₀ (pair U (pair Y₁ Y₂))) n v) L₃) ∧
      ∑ C : Fin L₃ → Fin n → β₀, iidPMF (channelExt (condDist μ Y₀ (pair U (pair Y₁ Y₂))) n v) L₃ C
        *
          (if ∀ m, ¬ zipSeq (zipSeq v x) (C m) ∈
            robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε₃ then 1 else 0) ≤ η₂) :
    ∃ (C : Fin L₀ → Fin n → υ) (D : Fin L₀ → (Fin L₁ → Fin n → β₁) × (Fin L₂ → Fin n → β₂))
      (E : Fin L₀ × (Fin L₁ × Fin L₂) → Fin L₃ → Fin n → β₀) (m₀ : (Fin n → α) → Fin L₀)
      (m₁₂ : (Fin n → α) → Fin L₁ × Fin L₂) (m₃ : (Fin n → α) → Fin L₃),
      ∑ x, iidPMF (dist μ X) n x * (if zbSeq (C (m₀ x)) ((D (m₀ x)).1 (m₁₂ x).1)
          ((D (m₀ x)).2 (m₁₂ x).2) x (E (m₀ x, m₁₂ x) (m₃ x)) ∈
            robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε₃ then 0 else 1) ≤
        ∑ x, iidPMF (dist μ X) n x *
          (if x ∈ robustTypicalSet (dist μ X) n ε₀ then 0 else 1) + η₀ + η₁ + η₂ := by
  have : Nonempty (Fin L₀) := ⟨⟨0, hL₀⟩⟩
  have : Nonempty (Fin L₁) := ⟨⟨0, hL₁⟩⟩
  have : Nonempty (Fin L₂) := ⟨⟨0, hL₂⟩⟩
  have : Nonempty (Fin L₃) := ⟨⟨0, hL₃⟩⟩
  obtain ⟨C, D, E, f₀, f₁, f₂, h⟩ := exists_three_layers (iidPMF_isPMF (hμ.dist X) n)
    (fun x => x ∈ robustTypicalSet (dist μ X) n ε₀) (iidPMF (iidPMF (dist μ U) n) L₀)
    (fun C x m => zipSeq x (C m) ∈ robustTypicalSet (dist μ (pair X U)) n ε₁)
    (fun C i => coverLaw (channelExt (condDist μ Y₁ U) n (C i))
      (channelExt (condDist μ Y₂ U) n (C i)) L₁ L₂)
    (fun C i D x (l : Fin L₁ × Fin L₂) => zipSeq (zipSeq (C i) (zipSeq x (D.1 l.1))) (D.2 l.2) ∈
      robustTypicalSet (triLaw μ U (pair X Y₁) Y₂) n ε₂)
    (fun C D i => iidPMF (channelExt (condDist μ Y₀ (pair U (pair Y₁ Y₂))) n
      (zipSeq (C i.1) (zipSeq ((D i.1).1 i.2.1) ((D i.1).2 i.2.2)))) L₃)
    (fun C D i E x m => zipSeq (zipSeq (zipSeq (C i.1) (zipSeq ((D i.1).1 i.2.1) ((D i.1).2 i.2.2)))
      x) (E m) ∈ robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε₃) hη₀ hη₁ hη₂
    (fun x hx => ⟨iidPMF_isPMF (iidPMF_isPMF (hμ.dist U) n) L₀,
      le_trans (le_of_eq (sum_congr rfl fun D _ => mul_ite_congr _ _ _ Iff.rfl)) (h₀ x hx)⟩)
    (fun C x j hR => by
      have h1 := comp_mem_robustTypicalSet hR Prod.swap
      have h2 : dist (dist μ (pair X U)) Prod.swap = dist μ (pair U X) := by
        rw [← dist_comp_eq]
        rfl
      rw [h2] at h1
      obtain ⟨hp, hs⟩ := h₁ (C j) x h1
      exact ⟨hp, le_trans (le_of_eq (sum_congr rfl fun D _ =>
        mul_ite_congr _ _ _ Prod.forall)) hs⟩)
    (fun C D x j l hR => by
      have h1 := comp_mem_robustTypicalSet hR
        (fun t : (υ × α × β₁) × β₂ => ((t.1.1, t.1.2.2, t.2), t.1.2.1))
      have h2 : dist (triLaw μ U (pair X Y₁) Y₂)
          (fun t : (υ × α × β₁) × β₂ => ((t.1.1, t.1.2.2, t.2), t.1.2.1)) =
          dist μ (pair (pair U (pair Y₁ Y₂)) X) := by
        rw [triLaw, ← dist_comp_eq]
        rfl
      rw [h2] at h1
      obtain ⟨hp, hs⟩ := h₂ _ x h1
      exact ⟨hp, le_trans (le_of_eq (sum_congr rfl fun D _ =>
        mul_ite_congr _ _ _ Iff.rfl)) hs⟩)
  refine ⟨C, D, E, f₀, f₁, f₂, ?_⟩
  convert h
  rfl

end Chain

/-! ### Exponential bounds -/

section Limits

/-- If `a < b` and `e^{nb} ≤ K L(n)`, then `exp(-L(n) c e^{-na}) → 0`, for `c > 0`. -/
lemma tendsto_exp_neg_mul_of_le {a b c K : ℝ} (hab : a < b) (hc : 0 < c) (hK : 0 < K) {L : ℕ → ℝ}
    (hL : ∀ n : ℕ, exp (n * b) ≤ K * L n) :
    Tendsto (fun n : ℕ => exp (-(L n * (c * exp (-(n * a)))))) atTop (𝓝 0) := by
  refine tendsto_exp_neg_atTop_nhds_zero.comp ?_
  have hlow : ∀ n : ℕ, c / K * exp (n * (b - a)) ≤ L n * (c * exp (-(n * a))) := fun n => by
    have e : exp (n * (b - a)) = exp (n * b) * exp (-(n * a)) := by
      rw [← exp_add]
      ring_nf
    have hpos := mul_pos hc (exp_pos (-(n * a)))
    have h1 := mul_le_mul_of_nonneg_right (hL n) hpos.le
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hK]
    nlinarith
  refine tendsto_atTop_mono hlow (Tendsto.const_mul_atTop (by positivity) ?_)
  exact tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hab))

/-- If `a < b` and `e^{nb} ≤ K L(n)`, then `e^{na}/L(n) → 0`. -/
lemma tendsto_exp_div_of_le {a b K : ℝ} (hab : a < b) {L : ℕ → ℝ}
    (hL0 : ∀ n, 0 < L n) (hL : ∀ n : ℕ, exp (n * b) ≤ K * L n) :
    Tendsto (fun n : ℕ => exp (n * a) / L n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => K * exp (-(n * (b - a)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) * (b - a)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hab)
    have h2 := (tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul K
    simpa using h2
  refine squeeze_zero (fun n => (div_pos (exp_pos _) (hL0 n)).le) (fun n => ?_) hlim
  rw [div_le_iff₀ (hL0 n)]
  have e : exp (n * a) = exp (-(n * (b - a))) * exp (n * b) := by
    rw [← exp_add]
    ring_nf
  rw [e]
  calc exp (-(n * (b - a))) * exp (n * b) ≤ exp (-(n * (b - a))) * (K * L n) :=
        mul_le_mul_of_nonneg_left (hL n) (exp_pos _).le
    _ = K * exp (-(n * (b - a))) * L n := by ring

/-- `e^{n R log 2} ≤ 2 · 2^⌊nR⌋`. -/
lemma exp_le_two_mul_two_pow_floor (n : ℕ) (R : ℝ) :
    exp (n * (R * log 2)) ≤ 2 * ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) := by
  have h := exp_le_two_pow_floor n R
  have e : exp (n * (R * log 2)) = 2 * exp (n * (R * log 2) - log 2) := by
    rw [exp_sub, exp_log two_pos]
    ring
  rw [e]
  linarith

/-- The floors of three nonnegative numbers add up to at most the floor of a larger number. -/
lemma floor_add_three_le (n : ℕ) {a b c R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≤ R) : ⌊n * a⌋₊ + ⌊n * b⌋₊ + ⌊n * c⌋₊ ≤ ⌊n * R⌋₊ := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hR : 0 ≤ (n : ℝ) * R := mul_nonneg hn (by linarith)
  refine Nat.le_floor ?_
  push_cast
  have h1 := Nat.floor_le (mul_nonneg hn ha)
  have h2 := Nat.floor_le (mul_nonneg hn hb)
  have h3 := Nat.floor_le (mul_nonneg hn hc)
  nlinarith

end Limits

/-! ### The code -/

section Code

variable {n L₀ L₁ L₂ L₀₁ L₀₂ M₁ M₂ : ℕ} {d₀ : α → β₀ → ℝ} {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ}

omit [Fintype Ω] [Fintype α] [Fintype υ] [Fintype β₀] [Fintype β₁] [Fintype β₂] in
/-- The code of the three layers of codebooks. -/
theorem exists_mdCode_of_chain (hc₁ : L₀ * L₁ * L₀₁ ≤ M₁) (hc₂ : L₀ * L₂ * L₀₂ ≤ M₂)
    [NeZero L₀] [NeZero L₁] [NeZero L₂] [NeZero L₀₁] [NeZero L₀₂]
    (D : Fin L₀ → (Fin L₁ → Fin n → β₁) × (Fin L₂ → Fin n → β₂))
    (E : Fin L₀ × (Fin L₁ × Fin L₂) → Fin (L₀₁ * L₀₂) → Fin n → β₀) (m₀ : (Fin n → α) → Fin L₀)
    (m₁₂ : (Fin n → α) → Fin L₁ × Fin L₂) (m₃ : (Fin n → α) → Fin (L₀₁ * L₀₂)) :
    ∃ c : MDCode M₁ M₂ n α β₀ β₁ β₂, ∀ x,
      c.dec₀ (c.enc₁ x, c.enc₂ x) = E (m₀ x, m₁₂ x) (m₃ x) ∧
      c.dec₁ (c.enc₁ x) = (D (m₀ x)).1 (m₁₂ x).1 ∧ c.dec₂ (c.enc₂ x) = (D (m₀ x)).2 (m₁₂ x).2 := by
  set e : Fin L₀₁ × Fin L₀₂ ≃ Fin (L₀₁ * L₀₂) := finProdFinEquiv with he
  obtain ⟨c, hc⟩ := MDCode.exists_of_index (α := α) (β₀ := β₀) (β₁ := β₁) (β₂ := β₂) (n := n)
    (ι₁ := Fin L₀ × Fin L₁ × Fin L₀₁) (ι₂ := Fin L₀ × Fin L₂ × Fin L₀₂) (M₁ := M₁) (M₂ := M₂)
    (by simpa [mul_assoc] using hc₁) (by simpa [mul_assoc] using hc₂)
    (fun x => (m₀ x, (m₁₂ x).1, (e.symm (m₃ x)).1)) (fun x => (m₀ x, (m₁₂ x).2, (e.symm (m₃ x)).2))
    (fun a => E (a.1.1, a.1.2.1, a.2.2.1) (e (a.1.2.2, a.2.2.2)))
    (fun a => (D a.1).1 a.2.1) (fun a => (D a.1).2 a.2.1)
  refine ⟨c, fun x => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hc x
  refine ⟨h0.trans ?_, h1, h2⟩
  simp

/-- The expectation of a function under the law of `T`. -/
lemma expect_dist {T : Type*} [Fintype T] (V : Ω → T) (g : T → ℝ) :
    expect (dist μ V) g = ∑ ω, μ ω * g (V ω) := by
  rw [expect, ← sum_dist_mul μ V g]
  exact sum_congr rfl fun a _ => mul_comm (g a) (dist μ V a)

omit [Fintype β₀] in
/-- The expected average distortion of sequences that are typical with the source: at most
`(1 + ε) E d(X, Y) + d_max P{not typical}`, by the typical average lemma. The decidability instances
of the event are arbitrary. -/
lemma sum_seqDistortion_le_of_typical [Finite β₀] (hμ : IsPMF μ) (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε)
    {Z : Type*} [Fintype Z] (V : Ω → Z) (t : (Fin n → α) → Fin n → Z) (pX : Z → α) (ρ : Z → β₀)
    (y : (Fin n → α) → Fin n → β₀) (hx : ∀ x i, pX (t x i) = x i) (hy : ∀ x i, ρ (t x i) = y x i)
    (hd : ∀ a b, 0 ≤ d₀ a b) {dec : ∀ x, Decidable (t x ∈ robustTypicalSet (dist μ V) n ε)} :
    ∑ x, iidPMF (dist μ X) n x * seqDistortion d₀ x (y x) ≤
      (1 + ε) * ∑ ω, μ ω * d₀ (pX (V ω)) (ρ (V ω)) + maxDistortion d₀ *
        ∑ x, iidPMF (dist μ X) n x *
          @ite ℝ (t x ∈ robustTypicalSet (dist μ V) n ε) (dec x) 0 1 := by
  classical
  have h3 := sum_mul_cost_le (iidPMF_isPMF (hμ.dist X) n) (hμ.dist V) hn hε t
    (g := fun z => d₀ (pX z) (ρ z)) (fun z => hd _ _)
    (F := fun x => seqDistortion d₀ x (y x))
    (fun x => by
      simp only [seqDistortion, hx, hy])
    (m := maxDistortion d₀) fun x => seqDistortion_le_maxDistortion d₀ hn _ _
  rw [expect_dist] at h3
  refine h3.trans (le_of_eq ?_)
  congr!

end Code

/-! ### The coding theorem -/

section Main

variable {d₀ : α → β₀ → ℝ} {d₁ : α → β₁ → ℝ} {d₂ : α → β₂ → ℝ}

open Classical in
/-- The code for one `n` from bounds for the three layers. -/
theorem exists_zb_code_of_bounds (hμ : IsPMF μ) {n M₁ M₂ L₀ L₁ L₂ L₀₁ L₀₂ : ℕ} {ε₀ ε₁ ε₂ ε : ℝ}
    {η₀ η₁ η₂ : ℝ} (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) (hL₀₁ : 0 < L₀₁) (hL₀₂ : 0 < L₀₂)
    (hc₁ : L₀ * L₁ * L₀₁ ≤ M₁) (hc₂ : L₀ * L₂ * L₀₂ ≤ M₂) (hη₀ : 0 ≤ η₀) (hη₁ : 0 ≤ η₁)
    (hη₂ : 0 ≤ η₂)
    (h₀ : ∀ x ∈ robustTypicalSet (dist μ X) n ε₀,
      ∑ C : Fin L₀ → Fin n → υ, iidPMF (iidPMF (dist μ U) n) L₀ C *
        (if ∀ m, ¬ zipSeq x (C m) ∈ robustTypicalSet (dist μ (pair X U)) n ε₁ then 1 else 0) ≤ η₀)
    (h₁ : ∀ (u : Fin n → υ) (x : Fin n → α),
      zipSeq u x ∈ robustTypicalSet (dist μ (pair U X)) n ε₁ →
      IsPMF (coverLaw (channelExt (condDist μ Y₁ U) n u) (channelExt (condDist μ Y₂ U) n u) L₁ L₂) ∧
      ∑ D, coverLaw (channelExt (condDist μ Y₁ U) n u) (channelExt (condDist μ Y₂ U) n u) L₁ L₂ D *
          (if ∀ l₁ l₂, ¬ zipSeq (zipSeq u (zipSeq x (D.1 l₁))) (D.2 l₂) ∈
            robustTypicalSet (triLaw μ U (pair X Y₁) Y₂) n ε₂ then 1 else 0) ≤ η₁)
    (h₂ : ∀ (v : Fin n → υ × β₁ × β₂) (x : Fin n → α),
      zipSeq v x ∈ robustTypicalSet (dist μ (pair (pair U (pair Y₁ Y₂)) X)) n ε₂ →
      ∑ C : Fin (L₀₁ * L₀₂) → Fin n → β₀,
        iidPMF (channelExt (condDist μ Y₀ (pair U (pair Y₁ Y₂))) n v) (L₀₁ * L₀₂) C *
          (if ∀ m, ¬ zipSeq (zipSeq v x) (C m) ∈
            robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε then 1 else 0) ≤ η₂) :
    ∃ (c : MDCode M₁ M₂ n α β₀ β₁ β₂) (t : (Fin n → α) → Fin n → ((υ × β₁ × β₂) × α) × β₀),
      (∀ x i, (t x i).1.2 = x i) ∧ (∀ x i, (t x i).2 = c.dec₀ (c.enc₁ x, c.enc₂ x) i) ∧
      (∀ x i, (t x i).1.1.2.1 = c.dec₁ (c.enc₁ x) i) ∧
      (∀ x i, (t x i).1.1.2.2 = c.dec₂ (c.enc₂ x) i) ∧
      ∑ x, iidPMF (dist μ X) n x *
        (if t x ∈ robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε then 0 else 1) ≤
        ∑ x, iidPMF (dist μ X) n x *
          (if x ∈ robustTypicalSet (dist μ X) n ε₀ then 0 else 1) + η₀ + η₁ + η₂ := by
  obtain ⟨ω₀⟩ : Nonempty Ω := Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)
  have : Nonempty υ := ⟨U ω₀⟩
  have : Nonempty β₀ := ⟨Y₀ ω₀⟩
  have : Nonempty β₁ := ⟨Y₁ ω₀⟩
  have : Nonempty β₂ := ⟨Y₂ ω₀⟩
  obtain ⟨C, D, E, m₀, m₁₂, m₃, hch⟩ := exists_zb_chain (Y₀ := Y₀) (ε₃ := ε) hμ hL₀ hL₁ hL₂
    (mul_pos hL₀₁ hL₀₂) hη₀ hη₁ hη₂ h₀ h₁ fun v x hvx =>
      ⟨iidPMF_isPMF (channelExt_condDist_isPMF hμ Y₀ _ fun i => dist_ne_zero_of_mem hμ hvx i) _,
        h₂ v x hvx⟩
  have : NeZero L₀ := ⟨hL₀.ne'⟩
  have : NeZero L₁ := ⟨hL₁.ne'⟩
  have : NeZero L₂ := ⟨hL₂.ne'⟩
  have : NeZero L₀₁ := ⟨hL₀₁.ne'⟩
  have : NeZero L₀₂ := ⟨hL₀₂.ne'⟩
  obtain ⟨c, hc⟩ := exists_mdCode_of_chain (α := α) (β₀ := β₀) hc₁ hc₂ D E m₀ m₁₂ m₃
  refine ⟨c, fun x => zbSeq (C (m₀ x)) ((D (m₀ x)).1 (m₁₂ x).1) ((D (m₀ x)).2 (m₁₂ x).2) x
    (E (m₀ x, m₁₂ x) (m₃ x)), fun x i => rfl, fun x i => ?_, fun x i => ?_, fun x i => ?_, hch⟩
  · rw [(hc x).1]
    rfl
  · rw [(hc x).2.1]
    rfl
  · rw [(hc x).2.2]
    rfl

open Classical in
omit [Fintype Ω] [Fintype υ] [Fintype β₀] [Fintype β₁] [Fintype β₂] in
/-- The probability of the source sequences that are not typical tends to zero. -/
lemma tendsto_sum_ite_not_typical {P : α → ℝ} (hP : IsPMF P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ∑ x, iidPMF P n x *
      (if x ∈ robustTypicalSet P n ε then (0 : ℝ) else 1)) atTop (𝓝 0) := by
  have h := tendsto_prob_robustTypicalSet hP hε
  have e : ∀ n : ℕ, ∑ x, iidPMF P n x * (if x ∈ robustTypicalSet P n ε then (0 : ℝ) else 1) =
      1 - prob (iidPMF P n) (robustTypicalSet P n ε) := fun n => by
    have hs : ∑ x, iidPMF P n x * (if x ∈ robustTypicalSet P n ε then (0 : ℝ) else 1) +
        prob (iidPMF P n) (robustTypicalSet P n ε) = ∑ x, iidPMF P n x := by
      rw [prob, ← univ_inter (robustTypicalSet P n ε), ← sum_ite_mem, ← sum_add_distrib]
      refine sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ robustTypicalSet P n ε <;> simp [hx]
    rw [(iidPMF_isPMF hP n).sum_eq_one] at hs
    linarith
  simp_rw [e]
  simpa using h.const_sub 1

/-- `e^{n (R + R') log 2} ≤ 4 · 2^⌊nR⌋ 2^⌊nR'⌋`. -/
lemma exp_le_four_mul_two_pow_floor (R R' : ℝ) (n : ℕ) : exp (n * ((R + R') * log 2)) ≤
    4 * (((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) * ((2 ^ ⌊n * R'⌋₊ : ℕ) : ℝ)) := by
  have e : exp (n * ((R + R') * log 2)) = exp (n * (R * log 2)) * exp (n * (R' * log 2)) := by
    rw [← exp_add]
    ring_nf
  rw [e]
  calc _ ≤ (2 * ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ)) * (2 * ((2 ^ ⌊n * R'⌋₊ : ℕ) : ℝ)) :=
        mul_le_mul (exp_le_two_mul_two_pow_floor n R) (exp_le_two_mul_two_pow_floor n R')
          (exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The error term of the middle layer tends to zero. -/
lemma tendsto_middle_term {J a₁ a₂ R R' : ℝ} (hJ : J < (R + R') * log 2) (h₁ : a₁ < R * log 2)
    (h₂ : a₂ < R' * log 2) :
    Tendsto (fun n : ℕ => 4 * (exp (n * J) / (((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) * ((2 ^ ⌊n * R'⌋₊ : ℕ) : ℝ))
      +
      exp (n * a₁) / ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) + exp (n * a₂) / ((2 ^ ⌊n * R'⌋₊ : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have ht1 := tendsto_exp_div_of_le (a := J) (b := (R + R') * log 2) (K := 4) hJ
    (L := fun n : ℕ => ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) * ((2 ^ ⌊n * R'⌋₊ : ℕ) : ℝ))
    (fun n => by positivity) (exp_le_four_mul_two_pow_floor R R')
  have ht2 := tendsto_exp_div_of_le (a := a₁) (b := R * log 2) (K := 2) h₁
    (L := fun n : ℕ => ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ)) (fun n => by positivity)
    fun n => exp_le_two_mul_two_pow_floor n R
  have ht3 := tendsto_exp_div_of_le (a := a₂) (b := R' * log 2) (K := 2) h₂
    (L := fun n : ℕ => ((2 ^ ⌊n * R'⌋₊ : ℕ) : ℝ)) (fun n => by positivity)
    fun n => exp_le_two_mul_two_pow_floor n R'
  have h := ((ht1.add ht2).add ht3).const_mul 4
  simpa using h

lemma add_four_le {a b c d θ : ℝ} (ha : a < θ / 4) (hb : b < θ / 4) (hc : c < θ / 4)
    (hd : d < θ / 4) : a + b + c + d ≤ θ := by
  linarith

open Classical in
/-- The codes for all large `n`, for abstract numbers of codewords in the layers. -/
theorem eventually_zb_code_aux (hμ : IsPMF μ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2) {J : ℝ}
    {L₀ L₁ L₂ L₀₁ L₀₂ M₁ M₂ : ℕ → ℕ} (hL₀ : ∀ n, 0 < L₀ n) (hL₁ : ∀ n, 0 < L₁ n) (hL₂ : ∀ n, 0 < L₂
      n)
    (hL₀₁ : ∀ n, 0 < L₀₁ n) (hL₀₂ : ∀ n, 0 < L₀₂ n) (hc₁ : ∀ n, L₀ n * L₁ n * L₀₁ n ≤ M₁ n)
    (hc₂ : ∀ n, L₀ n * L₂ n * L₀₂ n ≤ M₂ n)
    (hJ : J = I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ])
    (hJ' : J = I[X : Y₂ | U ; μ] + I[pair X Y₂ : Y₁ | U ; μ])
    (hη₀ : Tendsto (fun n : ℕ => exp (-((L₀ n : ℝ) * ((1 - 2 * ε / 5) * exp (-(n * (I[U : X ; μ] +
      2 * ε / 5 * (2 * log (Fintype.card υ))))))))) atTop (𝓝 0))
    (hη₁ : Tendsto (fun n : ℕ => 4 * (exp (n * (J + 2 * (4 * ε / 5 * (2 * (log (Fintype.card β₁) +
      log (Fintype.card β₂)))))) / ((L₁ n : ℝ) * (L₂ n : ℝ)) +
      exp (n * (I[X : Y₁ | U ; μ] + 3 * (4 * ε / 5 * (2 * (log (Fintype.card β₁) +
        log (Fintype.card β₂)))))) / (L₁ n : ℝ) +
      exp (n * (I[X : Y₂ | U ; μ] + 3 * (4 * ε / 5 * (2 * (log (Fintype.card β₁) +
        log (Fintype.card β₂)))))) / (L₂ n : ℝ))) atTop (𝓝 0))
    (hη₂ : Tendsto (fun n : ℕ => exp (-((L₀₁ n : ℝ) * (L₀₂ n : ℝ) * ((1 - ε) * exp (-(n *
      (I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ] + ε * (2 * log (Fintype.card β₀))))))))) atTop (𝓝 0))
    {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∃ (c : MDCode (M₁ n) (M₂ n) n α β₀ β₁ β₂)
      (t : (Fin n → α) → Fin n → ((υ × β₁ × β₂) × α) × β₀),
      (∀ x i, (t x i).1.2 = x i) ∧ (∀ x i, (t x i).2 = c.dec₀ (c.enc₁ x, c.enc₂ x) i) ∧
      (∀ x i, (t x i).1.1.2.1 = c.dec₁ (c.enc₁ x) i) ∧
      (∀ x i, (t x i).1.1.2.2 = c.dec₂ (c.enc₂ x) i) ∧
      ∑ x, iidPMF (dist μ X) n x *
        (if t x ∈ robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε then 0 else 1) ≤ θ :=
          by
  have hfirst := eventually_sum_first_codebook_le (ε₀ := ε / 5) (ε := 2 * ε / 5) hμ X U
    (by linarith) (by linarith) (by linarith)
  have htwo := eventually_sum_two_codebooks_le (X := X) (U := U) (Y₁ := Y₁) (Y₂ := Y₂)
    (ε₁ := 2 * ε / 5) (ε' := 3 * ε / 5) (ε := 4 * ε / 5) hμ (by linarith) (by linarith)
    (by linarith) (by linarith) hJ hJ'
  have hlast := eventually_sum_last_codebook_le (ε' := 4 * ε / 5) (ε := ε) hμ
    (pair U (pair Y₁ Y₂)) X Y₀ (by linarith) hε (by linarith)
  have hp := tendsto_sum_ite_not_typical (hμ.dist X) (show 0 < ε / 5 by positivity)
  have hsmall : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) → ∀ᶠ n in atTop, f n < θ / 4 := fun h =>
    (tendsto_order.1 h).2 _ (by positivity)
  filter_upwards [hfirst, htwo, hlast, hsmall hp, hsmall hη₀, hsmall hη₁, hsmall hη₂] with n h1 h2
    h3' a0 a1 a2 a3
  have hnn₁ : 0 ≤ 4 * (exp (n * (J + 2 * (4 * ε / 5 * (2 * (log (Fintype.card β₁) +
      log (Fintype.card β₂)))))) / ((L₁ n : ℝ) * (L₂ n : ℝ)) +
      exp (n * (I[X : Y₁ | U ; μ] + 3 * (4 * ε / 5 * (2 * (log (Fintype.card β₁) +
        log (Fintype.card β₂)))))) / (L₁ n : ℝ) +
      exp (n * (I[X : Y₂ | U ; μ] + 3 * (4 * ε / 5 * (2 * (log (Fintype.card β₁) +
        log (Fintype.card β₂)))))) / (L₂ n : ℝ)) := by positivity
  have h3e : ∀ (v : Fin n → υ × β₁ × β₂) (x : Fin n → α),
      zipSeq v x ∈ robustTypicalSet (dist μ (pair (pair U (pair Y₁ Y₂)) X)) n (4 * ε / 5) →
      ∑ C : Fin (L₀₁ n * L₀₂ n) → Fin n → β₀,
        iidPMF (channelExt (condDist μ Y₀ (pair U (pair Y₁ Y₂))) n v) (L₀₁ n * L₀₂ n) C *
          (if ∀ m, ¬ zipSeq (zipSeq v x) (C m) ∈
            robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε then 1 else 0) ≤
        exp (-((L₀₁ n : ℝ) * (L₀₂ n : ℝ) * ((1 - ε) * exp (-(n *
          (I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ] + ε * (2 * log (Fintype.card β₀)))))))) :=
    fun v x hvx => by
      have h := h3' v x hvx (L₀₁ n * L₀₂ n)
      rw [Nat.cast_mul (L₀₁ n) (L₀₂ n)] at h
      convert h
  obtain ⟨c, t, h1', h2', h3'', h4', hb⟩ := exists_zb_code_of_bounds (Y₀ := Y₀) (ε₀ := ε / 5)
    (ε₁ := 2 * ε / 5) (ε₂ := 4 * ε / 5) (ε := ε) hμ (hL₀ n) (hL₁ n) (hL₂ n) (hL₀₁ n) (hL₀₂ n)
    (hc₁ n) (hc₂ n) (exp_pos _).le hnn₁ (exp_pos _).le
    (fun x hx => le_trans (le_of_eq (sum_congr rfl fun C _ => mul_ite_congr _ _ _ Iff.rfl))
      (h1 x hx (L₀ n)))
    (fun u x hux => ⟨(h2 u x hux (hL₁ n) (hL₂ n)).1, le_trans (le_of_eq (sum_congr rfl fun C _ =>
      mul_ite_congr _ _ _ Iff.rfl)) (h2 u x hux (hL₁ n) (hL₂ n)).2⟩)
    h3e
  refine ⟨c, t, h1', h2', h3'', h4', hb.trans (add_four_le ?_ a1 a2 a3)⟩
  exact lt_of_eq_of_lt (sum_congr rfl fun _ _ => mul_ite_congr _ _ _ Iff.rfl) a0

open Classical in
/-- **Lecture 14, pages 14-28 and 14-29.** For `n` large there are codes whose sequences are jointly
typical except with probability at most `θ`, if the rates of the layers exceed the mutual
informations by a margin depending on `ε`. -/
theorem eventually_zb_code (hμ : IsPMF μ) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 2)
    {R₀ R₁₁ R₂₂ R₀₁ R₀₂ R₁ R₂ J δ : ℝ} (hR₀ : 0 ≤ R₀) (hR₁₁ : 0 ≤ R₁₁) (hR₂₂ : 0 ≤ R₂₂)
    (hR₀₁ : 0 ≤ R₀₁) (hR₀₂ : 0 ≤ R₀₂)
    (hδ : δ = ε * (2 * (log (Fintype.card υ) + log (Fintype.card β₀) + log (Fintype.card β₁) +
      log (Fintype.card β₂))))
    (hJ : J = I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ])
    (hJ' : J = I[X : Y₂ | U ; μ] + I[pair X Y₂ : Y₁ | U ; μ])
    (h₀ : I[U : X ; μ] + δ < R₀ * log 2) (h₁ : I[X : Y₁ | U ; μ] + 3 * δ < R₁₁ * log 2)
    (h₂ : I[X : Y₂ | U ; μ] + 3 * δ < R₂₂ * log 2) (h₁₂ : J + 2 * δ < (R₁₁ + R₂₂) * log 2)
    (h₃ : I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ] + δ < (R₀₁ + R₀₂) * log 2)
    (hs₁ : R₀ + R₁₁ + R₀₁ ≤ R₁) (hs₂ : R₀ + R₂₂ + R₀₂ ≤ R₂) {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ n : ℕ in atTop, ∃ (c : MDCode (2 ^ ⌊n * R₁⌋₊) (2 ^ ⌊n * R₂⌋₊) n α β₀ β₁ β₂)
      (t : (Fin n → α) → Fin n → ((υ × β₁ × β₂) × α) × β₀),
      (∀ x i, (t x i).1.2 = x i) ∧ (∀ x i, (t x i).2 = c.dec₀ (c.enc₁ x, c.enc₂ x) i) ∧
      (∀ x i, (t x i).1.1.2.1 = c.dec₁ (c.enc₁ x) i) ∧
      (∀ x i, (t x i).1.1.2.2 = c.dec₂ (c.enc₂ x) i) ∧
      ∑ x, iidPMF (dist μ X) n x *
        (if t x ∈ robustTypicalSet (triLaw μ (pair U (pair Y₁ Y₂)) X Y₀) n ε then 0 else 1) ≤ θ :=
          by
  have hcU : 0 ≤ log (Fintype.card υ) := log_natCast_nonneg _
  have hc₀ : 0 ≤ log (Fintype.card β₀) := log_natCast_nonneg _
  have hc₁ : 0 ≤ log (Fintype.card β₁) := log_natCast_nonneg _
  have hc₂ : 0 ≤ log (Fintype.card β₂) := log_natCast_nonneg _
  have hd₁ : 2 * ε / 5 * (2 * log (Fintype.card υ)) ≤ δ := by
    rw [hδ]
    nlinarith [mul_nonneg hε.le hc₀, mul_nonneg hε.le hc₁, mul_nonneg hε.le hc₂,
      mul_nonneg hε.le hcU]
  have hd₂ : 4 * ε / 5 * (2 * (log (Fintype.card β₁) + log (Fintype.card β₂))) ≤ δ := by
    rw [hδ]
    nlinarith [mul_nonneg hε.le hc₀, mul_nonneg hε.le hc₁, mul_nonneg hε.le hc₂,
      mul_nonneg hε.le hcU]
  have hd₃ : ε * (2 * log (Fintype.card β₀)) ≤ δ := by
    rw [hδ]
    nlinarith [mul_nonneg hε.le hc₀, mul_nonneg hε.le hc₁, mul_nonneg hε.le hc₂,
      mul_nonneg hε.le hcU]
  have hpos : ∀ (R : ℝ) (n : ℕ), 0 < 2 ^ ⌊(n : ℝ) * R⌋₊ := fun R n => by positivity
  have hcard : ∀ {R R' R'' S : ℝ}, 0 ≤ R → 0 ≤ R' → 0 ≤ R'' → R + R' + R'' ≤ S → ∀ n : ℕ,
      2 ^ ⌊(n : ℝ) * R⌋₊ * 2 ^ ⌊(n : ℝ) * R'⌋₊ * 2 ^ ⌊(n : ℝ) * R''⌋₊ ≤ 2 ^ ⌊(n : ℝ) * S⌋₊ :=
    fun h1 h2 h3 h4 n => by
      rw [← pow_add, ← pow_add]
      exact Nat.pow_le_pow_right two_pos (floor_add_three_le n h1 h2 h3 h4)
  exact eventually_zb_code_aux (L₀ := fun n => 2 ^ ⌊(n : ℝ) * R₀⌋₊)
    (L₁ := fun n => 2 ^ ⌊(n : ℝ) * R₁₁⌋₊) (L₂ := fun n => 2 ^ ⌊(n : ℝ) * R₂₂⌋₊)
    (L₀₁ := fun n => 2 ^ ⌊(n : ℝ) * R₀₁⌋₊) (L₀₂ := fun n => 2 ^ ⌊(n : ℝ) * R₀₂⌋₊)
    (M₁ := fun n => 2 ^ ⌊(n : ℝ) * R₁⌋₊) (M₂ := fun n => 2 ^ ⌊(n : ℝ) * R₂⌋₊) hμ hε hε₁
    (hpos R₀) (hpos R₁₁) (hpos R₂₂) (hpos R₀₁) (hpos R₀₂) (hcard hR₀ hR₁₁ hR₀₁ hs₁)
    (hcard hR₀ hR₂₂ hR₀₂ hs₂) hJ hJ'
    (tendsto_exp_neg_mul_of_le (b := R₀ * log 2) (K := 2) (by linarith) (by linarith) two_pos
      fun n => exp_le_two_mul_two_pow_floor n R₀)
    (tendsto_middle_term (by linarith) (by linarith) (by linarith))
    (tendsto_exp_neg_mul_of_le (b := (R₀₁ + R₀₂) * log 2) (K := 4) (by linarith) (by linarith)
      (by norm_num) (exp_le_four_mul_two_pow_floor R₀₁ R₀₂)) hθ

/-- The expected distortion is at most `D + τ` if the sequences are jointly typical except with
probability at most `θ`. -/
lemma sum_seqDistortion_le_of_fail {β' Z : Type*} [Finite β'] {d : α → β' → ℝ} (hμ : IsPMF μ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε) [Fintype Z] (V : Ω → Z) (t : (Fin n → α) → Fin n → Z)
    (pX : Z → α) (ρ : Z → β') (y : (Fin n → α) → Fin n → β') (hx : ∀ x i, pX (t x i) = x i)
    (hy : ∀ x i, ρ (t x i) = y x i) (hd : ∀ a b, 0 ≤ d a b) {θ D τ : ℝ}
    {dec : ∀ x, Decidable (t x ∈ robustTypicalSet (dist μ V) n ε)}
    (hf : ∑ x, iidPMF (dist μ X) n x *
      @ite ℝ (t x ∈ robustTypicalSet (dist μ V) n ε) (dec x) 0 1 ≤ θ)
    (hc : ∑ ω, μ ω * d (pX (V ω)) (ρ (V ω)) ≤ D)
    (h₁ : ε * ∑ ω, μ ω * d (pX (V ω)) (ρ (V ω)) ≤ τ / 2) (h₂ : maxDistortion d * θ ≤ τ / 2) :
    ∑ x, iidPMF (dist μ X) n x * seqDistortion d x (y x) ≤ D + τ := by
  have := Fintype.ofFinite β'
  obtain ⟨ω₀⟩ : Nonempty Ω := Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)
  have : Nonempty α := ⟨X ω₀⟩
  have : Nonempty β' := ⟨y (fun _ => X ω₀) ⟨0, hn⟩⟩
  have h := sum_seqDistortion_le_of_typical (X := X) (d₀ := d) (dec := dec) hμ hn hε V t pX ρ y hx
    hy hd
  have hm := maxDistortion_nonneg (d := d) hd
  have h3 := (mul_le_mul_of_nonneg_left hf hm).trans h₂
  refine h.trans ?_
  nlinarith

/-- A small positive number. -/
lemma exists_small_three {m₀ m₁ m₂ τ : ℝ} (h₀ : 0 ≤ m₀) (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (hτ : 0 < τ) :
    ∃ θ > 0, m₀ * θ ≤ τ / 2 ∧ m₁ * θ ≤ τ / 2 ∧ m₂ * θ ≤ τ / 2 := by
  refine ⟨τ / 2 / (m₀ + m₁ + m₂ + 1), by positivity, ?_, ?_, ?_⟩
  all_goals
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hτ.le h₀, mul_nonneg hτ.le h₁, mul_nonneg hτ.le h₂]

/-- The three distortions of a code whose sequences are jointly typical except with probability at
most `θ`. -/
lemma mdCode_distortions_le (hμ : IsPMF μ) {n M₁ M₂ : ℕ} (hn : 0 < n) {ε θ τ D₀ D₁ D₂ : ℝ}
    (hε : 0 ≤ ε) (hd₀ : ∀ a b, 0 ≤ d₀ a b) (hd₁ : ∀ a b, 0 ≤ d₁ a b) (hd₂ : ∀ a b, 0 ≤ d₂ a b)
    (c : MDCode M₁ M₂ n α β₀ β₁ β₂) (t : (Fin n → α) → Fin n → ((υ × β₁ × β₂) × α) × β₀)
    (ht₁ : ∀ x i, (t x i).1.2 = x i) (ht₂ : ∀ x i, (t x i).2 = c.dec₀ (c.enc₁ x, c.enc₂ x) i)
    (ht₃ : ∀ x i, (t x i).1.1.2.1 = c.dec₁ (c.enc₁ x) i)
    (ht₄ : ∀ x i, (t x i).1.1.2.2 = c.dec₂ (c.enc₂ x) i)
    {dec : ∀ x, Decidable (t x ∈ robustTypicalSet
      (dist μ (pair (pair (pair U (pair Y₁ Y₂)) X) Y₀)) n ε)}
    (hf : ∑ x, iidPMF (dist μ X) n x *
      @ite ℝ (t x ∈ robustTypicalSet (dist μ (pair (pair (pair U (pair Y₁ Y₂)) X) Y₀)) n ε) (dec x)
        0 1 ≤ θ)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂)
    (hε₀ : ε * ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ τ / 2) (hε₁ : ε * ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ τ / 2)
    (hε₂ : ε * ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ τ / 2) (hθ₀ : maxDistortion d₀ * θ ≤ τ / 2)
    (hθ₁ : maxDistortion d₁ * θ ≤ τ / 2) (hθ₂ : maxDistortion d₂ * θ ≤ τ / 2) :
    c.distortion₀ (dist μ X) d₀ ≤ D₀ + τ ∧ c.distortion₁ (dist μ X) d₁ ≤ D₁ + τ ∧
      c.distortion₂ (dist μ X) d₂ ≤ D₂ + τ :=
  ⟨sum_seqDistortion_le_of_fail hμ hn hε (pair (pair (pair U (pair Y₁ Y₂)) X) Y₀) t
      (fun z => z.1.2) (fun z => z.2) _ ht₁ ht₂ hd₀ hf hc₀ hε₀ hθ₀,
    sum_seqDistortion_le_of_fail hμ hn hε (pair (pair (pair U (pair Y₁ Y₂)) X) Y₀) t
      (fun z => z.1.2) (fun z => z.1.1.2.1) _ ht₁ ht₃ hd₁ hf hc₁ hε₁ hθ₁,
    sum_seqDistortion_le_of_fail hμ hn hε (pair (pair (pair U (pair Y₁ Y₂)) X) Y₀) t
      (fun z => z.1.2) (fun z => z.1.1.2.2) _ ht₁ ht₄ hd₂ hf hc₂ hε₂ hθ₂⟩

/-- **Lecture 14, page 14-29.** The coding theorem for the rates of the layers of Zhang–Berger
coding: the index `m₀` of `Uⁿ` is sent by both encoders, the indices `m₁₁`, `m₂₂` of `X̂₁ⁿ`, `X̂₂ⁿ`
by encoders 1 and 2, and the index `(m₀₁, m₀₂)` of `X̂₀ⁿ` is split between the two encoders. The
rates are in bits. -/
theorem isAchievableMD_of_split (hμ : IsPMF μ) (hd₀ : ∀ a b, 0 ≤ d₀ a b)
    (hd₁ : ∀ a b, 0 ≤ d₁ a b) (hd₂ : ∀ a b, 0 ≤ d₂ a b)
    {R₀ R₁₁ R₂₂ R₀₁ R₀₂ R₁ R₂ D₀ D₁ D₂ J : ℝ} (hR₀ : 0 ≤ R₀) (hR₁₁ : 0 ≤ R₁₁) (hR₂₂ : 0 ≤ R₂₂)
    (hR₀₁ : 0 ≤ R₀₁) (hR₀₂ : 0 ≤ R₀₂)
    (hJ : J = I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ])
    (hJ' : J = I[X : Y₂ | U ; μ] + I[pair X Y₂ : Y₁ | U ; μ])
    (h₀ : I[U : X ; μ] < R₀ * log 2) (h₁ : I[X : Y₁ | U ; μ] < R₁₁ * log 2)
    (h₂ : I[X : Y₂ | U ; μ] < R₂₂ * log 2) (h₁₂ : J < (R₁₁ + R₂₂) * log 2)
    (h₃ : I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ] < (R₀₁ + R₀₂) * log 2)
    (hs₁ : R₀ + R₁₁ + R₀₁ ≤ R₁) (hs₂ : R₀ + R₂₂ + R₀₂ ≤ R₂)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂) :
    IsAchievableMD (dist μ X) d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  obtain ⟨ω₀⟩ : Nonempty Ω := Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ)
  have : Nonempty α := ⟨X ω₀⟩
  have : Nonempty β₀ := ⟨Y₀ ω₀⟩
  have : Nonempty β₁ := ⟨Y₁ ω₀⟩
  have : Nonempty β₂ := ⟨Y₂ ω₀⟩
  refine isAchievableMD_of_eventually (by linarith) (by linarith) fun τ hτ => ?_
  have hcU : 0 ≤ log (Fintype.card υ) := log_natCast_nonneg _
  have hcb₀ : 0 ≤ log (Fintype.card β₀) := log_natCast_nonneg _
  have hcb₁ : 0 ≤ log (Fintype.card β₁) := log_natCast_nonneg _
  have hcb₂ : 0 ≤ log (Fintype.card β₂) := log_natCast_nonneg _
  have hm₀ := maxDistortion_nonneg (d := d₀) hd₀
  have hm₁ := maxDistortion_nonneg (d := d₁) hd₁
  have hm₂ := maxDistortion_nonneg (d := d₂) hd₂
  have hC₀ : 0 ≤ ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) := sum_nonneg fun ω _ =>
    mul_nonneg (hμ.nonneg ω) (hd₀ _ _)
  have hC₁ : 0 ≤ ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) := sum_nonneg fun ω _ =>
    mul_nonneg (hμ.nonneg ω) (hd₁ _ _)
  have hC₂ : 0 ≤ ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) := sum_nonneg fun ω _ =>
    mul_nonneg (hμ.nonneg ω) (hd₂ _ _)
  obtain ⟨C, hCd⟩ : ∃ C, C = 2 * (log (Fintype.card υ) + log (Fintype.card β₀) +
    log (Fintype.card β₁) + log (Fintype.card β₂)) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCd]
    positivity
  obtain ⟨K, hKd⟩ : ∃ K, K = ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) + ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) +
    ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hKd]
    positivity
  obtain ⟨S, hS0, hS₀, hS₁, hS₂, hS₁₂, hS₃⟩ : ∃ S > 0, S ≤ R₀ * log 2 - I[U : X ; μ] ∧
      S ≤ R₁₁ * log 2 - I[X : Y₁ | U ; μ] ∧ S ≤ R₂₂ * log 2 - I[X : Y₂ | U ; μ] ∧
      S ≤ (R₁₁ + R₂₂) * log 2 - J ∧
      S ≤ (R₀₁ + R₀₂) * log 2 - I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ] :=
    ⟨min (R₀ * log 2 - I[U : X ; μ]) (min (R₁₁ * log 2 - I[X : Y₁ | U ; μ])
      (min (R₂₂ * log 2 - I[X : Y₂ | U ; μ]) (min ((R₁₁ + R₂₂) * log 2 - J)
        ((R₀₁ + R₀₂) * log 2 - I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ])))),
      lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith)
        (lt_min (by linarith) (by linarith)))),
      min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))⟩
  obtain ⟨ε, hε0, hε₁, hε₂, hε₃⟩ : ∃ ε > 0, ε ≤ 1 / 2 ∧ ε * C ≤ S / 6 ∧ ε * K ≤ τ / 2 := by
    refine ⟨min (1 / 2) (min (S / (6 * (C + 1))) (τ / (2 * (K + 1)))),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min (1 / 2) (min (S / (6 * (C + 1))) (τ / (2 * (K + 1)))) ≤ S / (6 * (C + 1)) :=
        (min_le_right _ _).trans (min_le_left _ _)
      rw [le_div_iff₀ (by positivity)] at h
      have h0 : 0 < min (1 / 2) (min (S / (6 * (C + 1))) (τ / (2 * (K + 1)))) :=
        lt_min (by norm_num) (lt_min (by positivity) (by positivity))
      nlinarith
    · have h : min (1 / 2) (min (S / (6 * (C + 1))) (τ / (2 * (K + 1)))) ≤ τ / (2 * (K + 1)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h
      have h0 : 0 < min (1 / 2) (min (S / (6 * (C + 1))) (τ / (2 * (K + 1)))) :=
        lt_min (by norm_num) (lt_min (by positivity) (by positivity))
      nlinarith
  have hεC₀ : ε * ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ τ / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hε0.le) hε₃
    rw [hKd]
    linarith
  have hεC₁ : ε * ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ τ / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hε0.le) hε₃
    rw [hKd]
    linarith
  have hεC₂ : ε * ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ τ / 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hε0.le) hε₃
    rw [hKd]
    linarith
  obtain ⟨θ, hθ, hθ₀, hθ₁, hθ₂⟩ := exists_small_three hm₀ hm₁ hm₂ hτ
  have hδ : ε * C ≤ S / 6 := hε₂
  have hδ0 : 0 ≤ ε * C := mul_nonneg hε0.le hC0
  filter_upwards [eventually_zb_code (X := X) (U := U) (Y₀ := Y₀) (Y₁ := Y₁) (Y₂ := Y₂) hμ hε0 hε₁
    hR₀ hR₁₁ hR₂₂ hR₀₁ hR₀₂ (δ := ε * C) (by rw [hCd]) hJ hJ' (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) hs₁ hs₂ hθ, eventually_gt_atTop 0] with n hc hn
  obtain ⟨c, t, ht₁, ht₂, ht₃, ht₄, hf⟩ := hc
  exact ⟨c, mdCode_distortions_le hμ hn hε0.le hd₀ hd₁ hd₂ c t ht₁ ht₂ ht₃ ht₄
    hf hc₀ hc₁ hc₂ hεC₀ hεC₁ hεC₂ hθ₀ hθ₁ hθ₂⟩

/-- **Lecture 14, page 14-29: the Fourier–Motzkin step.** The rates of the layers for a rate pair
satisfying the conditions of the theorem. -/
lemma exists_zb_split {A B₁ B₂ J E r₁ r₂ : ℝ} (hA : 0 ≤ A) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hE : 0 ≤ E) (hJ : B₁ + B₂ ≤ J) (h₁ : A + B₁ < r₁) (h₂ : A + B₂ < r₂)
    (h₁₂ : 2 * A + J + E < r₁ + r₂) :
    ∃ r₀ r₁₁ r₂₂ r₀₁ r₀₂ : ℝ, 0 ≤ r₀ ∧ 0 ≤ r₁₁ ∧ 0 ≤ r₂₂ ∧ 0 ≤ r₀₁ ∧ 0 ≤ r₀₂ ∧ A < r₀ ∧ B₁ < r₁₁ ∧
      B₂ < r₂₂ ∧ J < r₁₁ + r₂₂ ∧ E < r₀₁ + r₀₂ ∧ r₀ + r₁₁ + r₀₁ = r₁ ∧ r₀ + r₂₂ + r₀₂ = r₂ := by
  obtain ⟨t, ht0, ht₁, ht₂, ht₃⟩ : ∃ t > 0, t < r₁ - A - B₁ ∧ t < r₂ - A - B₂ ∧
      2 * t < r₁ + r₂ - 2 * A - J - E :=
    ⟨min (r₁ - A - B₁) (min (r₂ - A - B₂) (r₁ + r₂ - 2 * A - J - E)) / 4,
      by have := lt_min (show 0 < r₁ - A - B₁ by linarith) (lt_min (show 0 < r₂ - A - B₂ by
        linarith)
          (show 0 < r₁ + r₂ - 2 * A - J - E by linarith))
         positivity,
      by have h1 := min_le_left (r₁ - A - B₁) (min (r₂ - A - B₂) (r₁ + r₂ - 2 * A - J - E))
         have := lt_min (show 0 < r₁ - A - B₁ by linarith) (lt_min (show 0 < r₂ - A - B₂ by
           linarith)
          (show 0 < r₁ + r₂ - 2 * A - J - E by linarith))
         linarith,
      by have h1 := (min_le_right (r₁ - A - B₁) (min (r₂ - A - B₂) (r₁ + r₂ - 2 * A - J - E))).trans
           (min_le_left _ _)
         have := lt_min (show 0 < r₁ - A - B₁ by linarith) (lt_min (show 0 < r₂ - A - B₂ by
           linarith)
          (show 0 < r₁ + r₂ - 2 * A - J - E by linarith))
         linarith,
      by have h1 := (min_le_right (r₁ - A - B₁) (min (r₂ - A - B₂) (r₁ + r₂ - 2 * A - J - E))).trans
           (min_le_right _ _)
         have := lt_min (show 0 < r₁ - A - B₁ by linarith) (lt_min (show 0 < r₂ - A - B₂ by
           linarith)
          (show 0 < r₁ + r₂ - 2 * A - J - E by linarith))
         linarith⟩
  set g₁ := r₁ - A - t - B₁ with hg₁
  set g₂ := r₂ - A - t - B₂ with hg₂
  have hg₁0 : 0 < g₁ := by linarith
  have hg₂0 : 0 < g₂ := by linarith
  set s := (J + (B₁ + g₁ + B₂ + g₂) - E) / 2 with hs
  have hsJ : J < s := by
    rw [hs]
    linarith
  have hsE : s < B₁ + g₁ + B₂ + g₂ - E := by
    rw [hs]
    linarith
  set a := (s - B₁ - B₂) / (g₁ + g₂) with ha
  have hgg : 0 < g₁ + g₂ := by linarith
  have ha0 : 0 < a := div_pos (by linarith) hgg
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hgg]
    linarith
  have hag : a * g₁ + a * g₂ = s - B₁ - B₂ := by
    rw [← mul_add, ha]
    field_simp
  have hp₁ : 0 < a * g₁ := mul_pos ha0 hg₁0
  have hp₂ : 0 < a * g₂ := mul_pos ha0 hg₂0
  have hq₁ : 0 < (1 - a) * g₁ := mul_pos (by linarith) hg₁0
  have hq₂ : 0 < (1 - a) * g₂ := mul_pos (by linarith) hg₂0
  have hq : (1 - a) * g₁ + (1 - a) * g₂ = g₁ + g₂ - (a * g₁ + a * g₂) := by ring
  refine ⟨A + t, B₁ + a * g₁, B₂ + a * g₂, (1 - a) * g₁, (1 - a) * g₂, by linarith, by linarith,
    by linarith, hq₁.le, hq₂.le, by linarith, by linarith, by linarith, by linarith, by linarith,
    ?_, ?_⟩
  · have : (1 - a) * g₁ = g₁ - a * g₁ := by ring
    rw [this, hg₁]
    ring
  · have : (1 - a) * g₂ = g₂ - a * g₂ := by ring
    rw [this, hg₂]
    ring

/-- `I(X; Y₁|U) + I(X, Y₁; Y₂|U)`, the term `J` of the middle layer, is symmetric in `Y₁` and `Y₂`,
and is equal to `I(X; Y₁, Y₂|U) + I(Y₁; Y₂|U)`. -/
lemma zb_J_eq (hμ : IsPMF μ) :
    I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ] =
      I[X : pair Y₁ Y₂ | U ; μ] + I[Y₁ : Y₂ | U ; μ] := by
  simp only [condMutualInfo_eq hμ]
  have e1 : H[pair U (pair (pair X Y₁) Y₂) ; μ] = H[pair U (pair X (pair Y₁ Y₂)) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × α × β₁ × β₂ => (t.1, (t.2.1, t.2.2.1), t.2.2.2))
      (fun a b h => by
        obtain ⟨a1, a2, a3, a4⟩ := a
        obtain ⟨b1, b2, b3, b4⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  rw [e1]
  ring

lemma zb_J_comm (hμ : IsPMF μ) :
    I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ] =
      I[X : Y₂ | U ; μ] + I[pair X Y₂ : Y₁ | U ; μ] := by
  simp only [condMutualInfo_eq hμ]
  have e1 : H[pair U (pair (pair X Y₁) Y₂) ; μ] = H[pair U (pair (pair X Y₂) Y₁) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × (α × β₂) × β₁ => (t.1, (t.2.1.1, t.2.2), t.2.1.2))
      (fun a b h => by
        obtain ⟨a1, ⟨a2, a3⟩, a4⟩ := a
        obtain ⟨b1, ⟨b2, b3⟩, b4⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  rw [e1]
  ring

/-- `I(X; Y₁|U) + I(X; Y₂|U) ≤ J`. -/
lemma zb_J_ge (hμ : IsPMF μ) :
    I[X : Y₁ | U ; μ] + I[X : Y₂ | U ; μ] ≤ I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ] := by
  have h := condMutualInfo_nonneg hμ Y₁ Y₂ (pair U X)
  rw [condMutualInfo_eq hμ] at h
  simp only [condMutualInfo_eq hμ]
  have e1 : H[pair (pair U X) Y₁ ; μ] = H[pair U (pair X Y₁) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × α × β₁ => ((t.1, t.2.1), t.2.2))
      (fun a b h => by
        obtain ⟨a1, a2, a3⟩ := a
        obtain ⟨b1, b2, b3⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  have e2 : H[pair (pair U X) Y₂ ; μ] = H[pair U (pair X Y₂) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × α × β₂ => ((t.1, t.2.1), t.2.2))
      (fun a b h => by
        obtain ⟨a1, a2, a3⟩ := a
        obtain ⟨b1, b2, b3⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  have e3 : H[pair (pair U X) (pair Y₁ Y₂) ; μ] = H[pair U (pair (pair X Y₁) Y₂) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × (α × β₁) × β₂ => ((t.1, t.2.1.1), t.2.1.2, t.2.2))
      (fun a b h => by
        obtain ⟨a1, ⟨a2, a3⟩, a4⟩ := a
        obtain ⟨b1, ⟨b2, b3⟩, b4⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  rw [e1, e2, e3] at h
  linarith

/-- `I(X; Y₀, Y₁, Y₂|U) + I(Y₁; Y₂|U) = J + I(X; Y₀|U, Y₁, Y₂)`. -/
lemma zb_sum_eq (hμ : IsPMF μ) :
    I[X : pair Y₀ (pair Y₁ Y₂) | U ; μ] + I[Y₁ : Y₂ | U ; μ] =
      I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ] + I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ] := by
  rw [zb_J_eq hμ]
  simp only [condMutualInfo_eq hμ]
  have e1 : H[pair (pair U (pair Y₁ Y₂)) X ; μ] = H[pair U (pair X (pair Y₁ Y₂)) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × α × β₁ × β₂ => ((t.1, t.2.2), t.2.1))
      (fun a b h => by
        obtain ⟨a1, a2, a3, a4⟩ := a
        obtain ⟨b1, b2, b3, b4⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  have e2 : H[pair (pair U (pair Y₁ Y₂)) Y₀ ; μ] = H[pair U (pair Y₀ (pair Y₁ Y₂)) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × β₀ × β₁ × β₂ => ((t.1, t.2.2), t.2.1))
      (fun a b h => by
        obtain ⟨a1, a2, a3, a4⟩ := a
        obtain ⟨b1, b2, b3, b4⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  have e3 : H[pair (pair U (pair Y₁ Y₂)) (pair X Y₀) ; μ] =
      H[pair U (pair X (pair Y₀ (pair Y₁ Y₂))) ; μ] :=
    entropyRV_eq_of_injective μ (fun t : υ × α × β₀ × β₁ × β₂ => ((t.1, t.2.2.2), t.2.1, t.2.2.1))
      (fun a b h => by
        obtain ⟨a1, a2, a3, a4, a5⟩ := a
        obtain ⟨b1, b2, b3, b4, b5⟩ := b
        simp only [Prod.mk.injEq] at h ⊢
        tauto) (fun _ => rfl)
  rw [e1, e2, e3]
  ring

/-- **Theorem 4 of Lecture 14 of [elgamal2010], page 14-27: the Zhang–Berger inner bound.** A rate
pair `(R₁, R₂)`, in bits, is achievable with the distortion triple `(D₀, D₁, D₂)` if
`R₁ > I(X; X̂₁, U)`, `R₂ > I(X; X̂₂, U)`,
`R₁ + R₂ > I(X; X̂₀, X̂₁, X̂₂|U) + 2 I(U; X) + I(X̂₁; X̂₂|U)` and `E dⱼ(X, X̂ⱼ) ≤ Dⱼ`. The random
variables are given on a finite probability space, and the mutual informations are in nats. -/
theorem isAchievableMD_zhangBerger (hμ : IsPMF μ) (hd₀ : ∀ a b, 0 ≤ d₀ a b)
    (hd₁ : ∀ a b, 0 ≤ d₁ a b) (hd₂ : ∀ a b, 0 ≤ d₂ a b) {R₁ R₂ D₀ D₁ D₂ : ℝ}
    (h₁ : I[X : pair Y₁ U ; μ] < R₁ * log 2) (h₂ : I[X : pair Y₂ U ; μ] < R₂ * log 2)
    (h₁₂ : I[X : pair Y₀ (pair Y₁ Y₂) | U ; μ] + 2 * I[U : X ; μ] + I[Y₁ : Y₂ | U ; μ] <
      (R₁ + R₂) * log 2)
    (hc₀ : ∑ ω, μ ω * d₀ (X ω) (Y₀ ω) ≤ D₀) (hc₁ : ∑ ω, μ ω * d₁ (X ω) (Y₁ ω) ≤ D₁)
    (hc₂ : ∑ ω, μ ω * d₂ (X ω) (Y₂ ω) ≤ D₂) :
    IsAchievableMD (dist μ X) d₀ d₁ d₂ R₁ R₂ D₀ D₁ D₂ := by
  have hl := log_pos one_lt_two
  have hA : I[X : U ; μ] = I[U : X ; μ] := mutualInfo_comm hμ X U
  have e₁ : I[X : pair Y₁ U ; μ] = I[U : X ; μ] + I[X : Y₁ | U ; μ] := by
    rw [chain_rule_mutualInfo₂ hμ, hA]
  have e₂ : I[X : pair Y₂ U ; μ] = I[U : X ; μ] + I[X : Y₂ | U ; μ] := by
    rw [chain_rule_mutualInfo₂ hμ, hA]
  have eS := zb_sum_eq (X := X) (U := U) (Y₀ := Y₀) (Y₁ := Y₁) (Y₂ := Y₂) hμ
  have hGe := zb_J_ge (X := X) (U := U) (Y₁ := Y₁) (Y₂ := Y₂) hμ
  obtain ⟨r₀, r₁₁, r₂₂, r₀₁, r₀₂, h0, h1, h2, h3, h4, a0, a1, a2, a3, a4, s₁, s₂⟩ :=
    exists_zb_split (A := I[U : X ; μ]) (B₁ := I[X : Y₁ | U ; μ]) (B₂ := I[X : Y₂ | U ; μ])
      (J := I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ])
      (E := I[X : Y₀ | pair U (pair Y₁ Y₂) ; μ]) (r₁ := R₁ * log 2) (r₂ := R₂ * log 2)
      (mutualInfo_nonneg hμ _ _) (condMutualInfo_nonneg hμ _ _ _) (condMutualInfo_nonneg hμ _ _ _)
      (condMutualInfo_nonneg hμ _ _ _) (by linarith) (by linarith) (by linarith) (by linarith)
  have hdiv : ∀ r : ℝ, r / log 2 * log 2 = r := fun r => div_mul_cancel₀ r hl.ne'
  have hle : ∀ {a b c r : ℝ}, a + b + c = r * log 2 → a / log 2 + b / log 2 + c / log 2 ≤ r :=
    fun {a b c r} h => by
      rw [← add_div, ← add_div, h, mul_div_assoc, div_self hl.ne', mul_one]
  refine isAchievableMD_of_split (J := I[X : Y₁ | U ; μ] + I[pair X Y₁ : Y₂ | U ; μ]) hμ hd₀ hd₁ hd₂
    (R₀ := r₀ / log 2) (R₁₁ := r₁₁ / log 2) (R₂₂ := r₂₂ / log 2) (R₀₁ := r₀₁ / log 2)
    (R₀₂ := r₀₂ / log 2) (div_nonneg h0 hl.le) (div_nonneg h1 hl.le) (div_nonneg h2 hl.le)
    (div_nonneg h3 hl.le) (div_nonneg h4 hl.le) rfl (zb_J_comm hμ) ?_ ?_ ?_ ?_ ?_
    (hle s₁) (hle s₂) hc₀ hc₁ hc₂
  · rwa [hdiv]
  · rwa [hdiv]
  · rwa [hdiv]
  · rwa [← add_div, hdiv]
  · rwa [← add_div, hdiv]

end Main

end InfoTheory
