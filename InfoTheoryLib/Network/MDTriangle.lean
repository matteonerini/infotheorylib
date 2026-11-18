/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BergerTungOuter
public import InfoTheoryLib.Network.MDLine

/-!
# Multiple description networks: the triangular network

Theorem 2 of Lecture 21 of El Gamal and Kim, due to Yamamoto. The nodes are `0`, the source, and `1`
and `2`, and the edges are `(0, 1)`, `(0, 2)` and `(1, 2)`.

## Main definitions

* `triEdges`: the triangular network.
* `IsTriLaw`, `triInner`: the region of Theorem 2. The law of `(X, U, X̂₁, X̂₂)` is any law with the
  marginal `P`; only the pairs `(U, X̂₁)` and `(U, X̂₂)` matter, as the notes remark on page 21-10.

## Main statements

* `isAchievableMDN_tri`: achievability.
* `triInner_subset_mdnRegion`: **the inner bound**.
* `exists_triInner_of_mem_mdnRegion`: **the converse**, with `Dₗ + ε` and `R + ε`, since there is
  no bound on the size of the alphabet of `U`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

variable {α : Type u} [Fintype α] {β : Fin 3 → Type*} [∀ l, Fintype (β l)]

/-- The edges of the triangular network. -/
def triEdges : Finset (Fin 3 × Fin 3) := {(0, 1), (0, 2), (1, 2)}

/-- A law for Theorem 2 of Lecture 21: the law of `(X, U, X̂₁, X̂₂)` with the source law `P`. -/
structure IsTriLaw {υ : Type u} [Fintype υ] (P : α → ℝ) (μ : α × υ × β 1 × β 2 → ℝ) : Prop where
  /-- It is a law. -/
  isPMF : IsPMF μ
  /-- The law of the source. -/
  fst : dist μ Prod.fst = P

/-- **Theorem 2 of Lecture 21 of [elgamal2010], page 21-8: the region at the distortions `D`.** In
the labels of Lean, `R 1 2 ≥ I(U; X)`, `R 0 1 ≥ I(U, X̂₁; X)` and `R 0 2 ≥ I(X̂₂; X | U)`, in bits.
-/
def triInner (P : α → ℝ) (d : ∀ l, α → β l → ℝ) (D : Fin 3 → ℝ) : Set (Fin 3 → Fin 3 → ℝ) :=
  {R | (∀ j k, 0 ≤ R j k) ∧ (∀ j k, (j, k) ∉ triEdges → R j k = 0) ∧
    ∃ (υ : Type u) (_ : Fintype υ) (μ : α × υ × β 1 × β 2 → ℝ), IsTriLaw P μ ∧
    I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.1 ; μ] ≤ R 1 2 * log 2 ∧
    I[Prod.fst : pair (fun z : α × υ × β 1 × β 2 => z.2.2.1) (fun z => z.2.1) ; μ] ≤
      R 0 1 * log 2 ∧
    I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.2 | fun z => z.2.1 ; μ] ≤ R 0 2 * log 2 ∧
    ∑ z, μ z * d 1 z.1 z.2.2.1 ≤ D 1 ∧ ∑ z, μ z * d 2 z.1 z.2.2.2 ≤ D 2}

/-! ### One layer -/

section Layer

universe a

variable {Ω υ δ : Type*} {γ : Type a} [Fintype Ω] [Fintype υ] [Fintype γ] [Fintype δ] [Nonempty δ]
  {μ : Ω → ℝ}

open Classical in
/-- **One layer of a superposition code.** Let `r > I(X; Y | V)`. For all large `n`, if the
sequences of the previous layers are typical with the source on a set `G`, one can choose `e^{n r}`
codewords for each previous index, and a codeword for each source sequence, that are typical with
them, except on a set of probability `η`. -/
theorem exists_cond_layer (hμ : IsPMF μ) (V : Ω → υ) (X : Ω → γ) (Y : Ω → δ) {r : ℝ}
    (hr : I[X : Y | V ; μ] < r) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' > 0, ∀ η > 0, ∀ᶠ n : ℕ in atTop, ∀ (A : Type a) (I₀ : Type) [Fintype A] [Finite I₀]
      {w : A → ℝ} (_ : IsPMF w) (e : A → I₀) (G : A → Prop) (v : I₀ → Fin n → υ) (x : A → Fin n →
        γ),
      (∀ t, G t → zipSeq (v (e t)) (x t) ∈ robustTypicalSet (dist μ (pair V X)) n ε') →
      ∃ (D : I₀ → Fin ⌈exp ((n : ℝ) * r)⌉₊ → Fin n → δ) (f : A → Fin ⌈exp ((n : ℝ) * r)⌉₊),
        ∑ t, w t * (if G t ∧ zipSeq (zipSeq (v (e t)) (x t)) (D (e t) (f t)) ∈
          robustTypicalSet (triLaw μ V X Y) n ε then 0 else 1) ≤
          ∑ t, w t * (if G t then 0 else 1) + η := by
  set Ik := I[X : Y | V ; μ] with hIk
  set c := log (Fintype.card δ) with hc
  have hc0 : 0 ≤ c := log_natCast_nonneg _
  set g := r - Ik with hg
  have hg0 : 0 < g := sub_pos.2 hr
  set ε₁ := min (min ε (1 / 2)) (g / (4 * (c + 1))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (lt_min hε (by norm_num)) (by positivity)
  have hε₁ε : ε₁ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hε₁2 : ε₁ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε₁g : ε₁ * (2 * c) ≤ g / 2 := by
    have h₁ : ε₁ ≤ g / (4 * (c + 1)) := min_le_right _ _
    calc ε₁ * (2 * c) ≤ g / (4 * (c + 1)) * (2 * c) :=
          mul_le_mul_of_nonneg_right h₁ (by positivity)
      _ ≤ g / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  refine ⟨ε₁ / 2, half_pos hε₁0, fun η hη => ?_⟩
  have hb := eventually_sum_last_codebook_le hμ V X Y (ε := ε₁) (half_lt_self hε₁0) hε₁0
    (by linarith)
  have hlim := tendsto_exp_neg_layer (a := Ik + g / 2) (b := r) (c := 1 / 2)
    (by simp only [hg]; linarith) (by norm_num)
  filter_upwards [hb, (tendsto_order.1 hlim).2 η hη, eventually_ge_atTop 0] with n hlast hsmall _
    A I₀ _ _ w hw e G v x hG
  have hLpos : 0 < ⌈exp ((n : ℝ) * r)⌉₊ := Nat.ceil_pos.2 (exp_pos _)
  have hne𝒟 : Nonempty (Fin ⌈exp ((n : ℝ) * r)⌉₊ → Fin n → δ) :=
    ⟨fun _ _ => Classical.arbitrary _⟩
  have hneJ : Nonempty (Fin ⌈exp ((n : ℝ) * r)⌉₊) := ⟨⟨0, hLpos⟩⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨D, f, hD⟩ := exists_layer hw e (fun t => G t)
    (fun i => iidPMF (channelExt (condDist μ Y V) n (v i)) ⌈exp ((n : ℝ) * r)⌉₊)
    (fun i D t j => zipSeq (zipSeq (v i) (x t)) (D j) ∈
      robustTypicalSet (triLaw μ V X Y) n ε₁) hη.le (fun t ht => by
      have hx := hG t ht
      refine ⟨iidPMF_isPMF (channelExt_condDist_isPMF hμ Y V (dist_ne_zero_of_mem hμ hx)) _, ?_⟩
      have hl' := hlast _ _ hx ⌈exp ((n : ℝ) * r)⌉₊
      refine le_trans (le_of_eq (sum_congr rfl fun D _ => ?_)) (hl'.trans (le_trans ?_ hsmall.le))
      · congr!
      refine exp_le_exp.2 (neg_le_neg ?_)
      have h₁ : (1 / 2 : ℝ) * exp (-(n * (Ik + g / 2))) ≤
          (1 - ε₁) * exp (-(n * (Ik + ε₁ * (2 * c)))) := by
        refine mul_le_mul (by linarith) (exp_le_exp.2 ?_) (exp_pos _).le (by linarith)
        have : (n : ℝ) * (ε₁ * (2 * c)) ≤ n * (g / 2) := mul_le_mul_of_nonneg_left hε₁g hn0
        nlinarith
      exact mul_le_mul (Nat.le_ceil _) h₁ (by positivity) (by positivity))
  refine ⟨D, f, ?_⟩
  have hsub : ∀ t, (if G t ∧ zipSeq (zipSeq (v (e t)) (x t)) (D (e t) (f t)) ∈
      robustTypicalSet (triLaw μ V X Y) n ε then (0 : ℝ) else 1) ≤
      if G t ∧ zipSeq (zipSeq (v (e t)) (x t)) (D (e t) (f t)) ∈
        robustTypicalSet (triLaw μ V X Y) n ε₁ then 0 else 1 := fun t => by
    by_cases h : G t ∧ zipSeq (zipSeq (v (e t)) (x t)) (D (e t) (f t)) ∈
        robustTypicalSet (triLaw μ V X Y) n ε₁
    · have h₂ := robustTypicalSet_mono (hμ.dist _).nonneg hε₁ε h.2
      rw [ite_eq_left ⟨h.1, h₂⟩, ite_eq_left h]
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  refine (sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hsub t) (hw.nonneg t)).trans ?_
  convert hD

open Classical in
/-- **The covering of the triangular network.** The first layer has a rate above `I(X; U)`, and two
layers on it have rates above `I(X; Y₁ | U)` and `I(X; Y₂ | U)`. -/
theorem exists_tri_cover {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] [Nonempty β₁] [Nonempty β₂]
    [Nonempty υ] (hμ : IsPMF μ) (X : Ω → γ) (U : Ω → υ) (Y₁ : Ω → β₁) (Y₂ : Ω → β₂) {ru r₁ r₂ : ℝ}
    (hu : I[X : U ; μ] < ru) (h₁ : I[X : Y₁ | U ; μ] < r₁) (h₂ : I[X : Y₂ | U ; μ] < r₂)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∃ (fu : (Fin n → γ) → Fin ⌈exp ((n : ℝ) * ru)⌉₊)
      (f₁ : (Fin n → γ) → Fin ⌈exp ((n : ℝ) * r₁)⌉₊)
      (f₂ : (Fin n → γ) → Fin ⌈exp ((n : ℝ) * r₂)⌉₊)
      (Du : Fin ⌈exp ((n : ℝ) * ru)⌉₊ → Fin n → υ)
      (D₁ : Fin ⌈exp ((n : ℝ) * ru)⌉₊ → Fin ⌈exp ((n : ℝ) * r₁)⌉₊ → Fin n → β₁)
      (D₂ : Fin ⌈exp ((n : ℝ) * ru)⌉₊ → Fin ⌈exp ((n : ℝ) * r₂)⌉₊ → Fin n → β₂),
      ∑ x, iidPMF (dist μ X) n x * (if
        zipSeq (zipSeq (Du (fu x)) x) (D₁ (fu x) (f₁ x)) ∈
          robustTypicalSet (triLaw μ U X Y₁) n ε ∧
        zipSeq (zipSeq (Du (fu x)) x) (D₂ (fu x) (f₂ x)) ∈
          robustTypicalSet (triLaw μ U X Y₂) n ε then 0 else 1) ≤ η := by
  obtain ⟨ε₁, hε₁0, hl₁⟩ := exists_cond_layer hμ U X Y₁ h₁ hε
  obtain ⟨ε₂, hε₂0, hl₂⟩ := exists_cond_layer hμ U X Y₂ h₂ hε
  set εb := min ε₁ ε₂ with hεb
  have hεb0 : 0 < εb := lt_min hε₁0 hε₂0
  have hu' : I[X : U | fun _ : Ω => () ; μ] < ru := by
    rw [condMutualInfo_const hμ]
    exact hu
  obtain ⟨εa, hεa0, hla⟩ := exists_cond_layer hμ (fun _ : Ω => ()) X U hu' hεb0
  have hη4 : 0 < η / 4 := by positivity
  have hPp : IsPMF (dist μ X) := hμ.dist X
  have htyp := tendsto_prob_robustTypicalSet hPp hεa0
  have ht : Tendsto (fun n => 1 - prob (iidPMF (dist μ X) n)
      (robustTypicalSet (dist μ X) n εa)) atTop (𝓝 0) := by
    simpa using htyp.const_sub 1
  filter_upwards [hla (η / 4) hη4, hl₁ (η / 4) hη4, hl₂ (η / 4) hη4,
    (tendsto_order.1 ht).2 (η / 4) hη4] with n ha b₁ b₂ hst
  have hw := iidPMF_isPMF hPp n
  set T₀ := robustTypicalSet (dist μ X) n εa with hT₀
  -- the first layer
  obtain ⟨Du₀, fu, hDu⟩ := ha (Fin n → γ) Unit hw (fun _ => ()) (fun x => x ∈ T₀)
    (fun _ _ => ()) id (fun x hx => by
      have h₃ := comp_mem_robustTypicalSet hx fun a => ((), a)
      have e : dist μ (pair (fun _ : Ω => ()) X) = dist (dist μ X) fun a => ((), a) := by
        rw [← dist_comp_eq]
        rfl
      rw [e]
      exact h₃)
  set Du : Fin ⌈exp ((n : ℝ) * ru)⌉₊ → Fin n → υ := Du₀ () with hDu₀
  set R₀ : (Fin n → γ) → Prop := fun x => x ∈ T₀ ∧
    zipSeq (zipSeq (fun _ => ()) x) (Du (fu x)) ∈
      robustTypicalSet (triLaw μ (fun _ : Ω => ()) X U) n εb with hR₀
  have hR₀t : ∀ x, R₀ x → zipSeq (Du (fu x)) x ∈ robustTypicalSet (dist μ (pair U X)) n εb :=
    fun x hx => by
      have h₃ := comp_mem_robustTypicalSet hx.2 fun w : (Unit × γ) × υ => (w.2, w.1.2)
      have e : dist μ (pair U X) = dist (triLaw μ (fun _ : Ω => ()) X U)
          fun w : (Unit × γ) × υ => (w.2, w.1.2) := by
        rw [triLaw, ← dist_comp_eq]
        rfl
      rw [e]
      exact h₃
  have hDu' : ∑ x, iidPMF (dist μ X) n x * (if R₀ x then (0 : ℝ) else 1) ≤
      ∑ x, iidPMF (dist μ X) n x * (if x ∈ T₀ then (0 : ℝ) else 1) + η / 4 := by
    convert hDu
    rfl
  -- the second layer
  obtain ⟨D₁, f₁, hD₁⟩ := b₁ (Fin n → γ) _ hw fu R₀ Du id fun x hx =>
    robustTypicalSet_mono (hμ.dist _).nonneg (min_le_left _ _) (hR₀t x hx)
  set R₁ : (Fin n → γ) → Prop := fun x => R₀ x ∧
    zipSeq (zipSeq (Du (fu x)) x) (D₁ (fu x) (f₁ x)) ∈
      robustTypicalSet (triLaw μ U X Y₁) n ε with hR₁
  have hD₁' : ∑ x, iidPMF (dist μ X) n x * (if R₁ x then (0 : ℝ) else 1) ≤
      ∑ x, iidPMF (dist μ X) n x * (if R₀ x then (0 : ℝ) else 1) + η / 4 := by
    convert hD₁
    rfl
  -- the third layer
  obtain ⟨D₂, f₂, hD₂⟩ := b₂ (Fin n → γ) _ hw fu R₁ Du id fun x hx =>
    robustTypicalSet_mono (hμ.dist _).nonneg (min_le_right _ _) (hR₀t x hx.1)
  set R₂ : (Fin n → γ) → Prop := fun x => R₁ x ∧
    zipSeq (zipSeq (Du (fu x)) x) (D₂ (fu x) (f₂ x)) ∈
      robustTypicalSet (triLaw μ U X Y₂) n ε with hR₂
  have hD₂' : ∑ x, iidPMF (dist μ X) n x * (if R₂ x then (0 : ℝ) else 1) ≤
      ∑ x, iidPMF (dist μ X) n x * (if R₁ x then (0 : ℝ) else 1) + η / 4 := by
    convert hD₂
    rfl
  refine ⟨fu, f₁, f₂, Du, D₁, D₂, ?_⟩
  have hT : ∑ x, iidPMF (dist μ X) n x * (if x ∈ T₀ then (0 : ℝ) else 1) ≤ η / 4 := by
    refine le_trans (le_of_eq ?_) hst.le
    have h2 : prob (iidPMF (dist μ X) n) T₀ = ∑ x, if x ∈ T₀ then iidPMF (dist μ X) n x else 0 := by
      rw [sum_ite_mem, univ_inter]
      rfl
    rw [h2]
    calc ∑ x, iidPMF (dist μ X) n x * (if x ∈ T₀ then (0 : ℝ) else 1)
        = ∑ x, (iidPMF (dist μ X) n x - if x ∈ T₀ then iidPMF (dist μ X) n x else 0) :=
          sum_congr rfl fun x _ => by split_ifs <;> simp
      _ = _ := by rw [sum_sub_distrib, hw.sum_eq_one]
  have hsub : ∀ x, (if zipSeq (zipSeq (Du (fu x)) x) (D₁ (fu x) (f₁ x)) ∈
        robustTypicalSet (triLaw μ U X Y₁) n ε ∧
      zipSeq (zipSeq (Du (fu x)) x) (D₂ (fu x) (f₂ x)) ∈
        robustTypicalSet (triLaw μ U X Y₂) n ε then (0 : ℝ) else 1) ≤
      if R₂ x then 0 else 1 := fun x => by
    by_cases h : R₂ x
    · rw [ite_eq_left h, ite_eq_left ⟨h.1.2, h.2⟩]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  refine (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hsub x) (hw.nonneg x)).trans ?_
  linarith

end Layer

/-! ### Achievability -/

section Achievability

variable [∀ l, Nonempty (β l)] {P : α → ℝ} {d : ∀ l, α → β l → ℝ}

omit [Fintype α] [∀ l, Fintype (β l)] [∀ l, Nonempty (β l)] in
/-- The ceiling of a large exponential is at most twice the exponential. -/
lemma ceil_exp_le {x : ℝ} (hx : 0 ≤ x) : (⌈exp x⌉₊ : ℝ) ≤ exp (log 2 + x) := by
  have h₂ : (⌈exp x⌉₊ : ℝ) < exp x + 1 := Nat.ceil_lt_add_one (exp_pos _).le
  have h₃ : 1 ≤ exp x := one_le_exp hx
  rw [exp_add, exp_log (by norm_num)]
  linarith

/-- The sum of a function over a typical triple. -/
lemma sum_le_of_mem_triLaw {Ω υ γ δ : Type*} [Fintype Ω] [Fintype υ] [Fintype γ] [Fintype δ]
    {μ : Ω → ℝ} (_hμ : IsPMF μ) (V : Ω → υ) (X : Ω → γ) (Y : Ω → δ) (g : γ → δ → ℝ)
    (hg : ∀ a b, 0 ≤ g a b) {n : ℕ} {ε : ℝ} {v : Fin n → υ} {x : Fin n → γ} {y : Fin n → δ}
    (h : zipSeq (zipSeq v x) y ∈ robustTypicalSet (triLaw μ V X Y) n ε) :
    ∑ i, g (x i) (y i) ≤ n * ((1 + ε) * ∑ ω, μ ω * g (X ω) (Y ω)) := by
  have h₁ := sum_le_card_mul_of_mem_robustTypicalSet h
    (g := fun w : (υ × γ) × δ => g w.1.2 w.2) fun w => hg _ _
  have e₂ : expect (triLaw μ V X Y) (fun w : (υ × γ) × δ => g w.1.2 w.2) =
      ∑ ω, μ ω * g (X ω) (Y ω) := by
    rw [expect]
    simp only [mul_comm (g _ _)]
    rw [triLaw, sum_dist_mul]
    rfl
  rw [e₂] at h₁
  exact h₁

omit [Fintype α] [(l : Fin 3) → Fintype (β l)] in
/-- The code of the triangular network: the edge `(0, 1)` carries the first two indices, the edge
`(0, 2)` the third one, and the edge `(1, 2)` the first one. -/
lemma exists_tri_code {n Lu L₁ L₂ : ℕ} [NeZero Lu] [NeZero L₁] [NeZero L₂]
    {M : Fin 3 → Fin 3 → ℕ} (hM : ∀ j k, 0 < M j k) (h₀₁ : Lu * L₁ ≤ M 0 1) (h₀₂ : L₂ ≤ M 0 2)
    (h₁₂ : Lu ≤ M 1 2) (fu : (Fin n → α) → Fin Lu) (f₁ : (Fin n → α) → Fin L₁)
    (f₂ : (Fin n → α) → Fin L₂) (D₁ : Fin Lu → Fin L₁ → Fin n → β 1)
    (D₂ : Fin Lu → Fin L₂ → Fin n → β 2) :
    ∃ c : MDNetCode (0 : Fin 3) M n α β, (∀ x, c.out x 1 = D₁ (fu x) (f₁ x)) ∧
      ∀ x, c.out x 2 = D₂ (fu x) (f₂ x) := by
  classical
  let T := Fin Lu × Fin L₁ × Fin L₂
  let part : Fin 3 → Fin 3 → T → T := fun j k t =>
    if j = 0 ∧ k = 1 then (t.1, t.2.1, 0) else if j = 0 ∧ k = 2 then (0, 0, t.2.2)
    else if j = 1 ∧ k = 2 then (t.1, 0, 0) else 0
  let know : Fin 3 → T → T := fun k t =>
    if k = 1 then (t.1, t.2.1, 0) else if k = 2 then (t.1, 0, t.2.2) else t
  let merge : ∀ k : Fin 3, (∀ j, j < k → T) → T := fun k w =>
    if h₁ : k = 1 then w 0 (by subst h₁; decide)
    else if h₂ : k = 2 then ((w 1 (by subst h₂; decide)).1, 0, (w 0 (by subst h₂; decide)).2.2)
    else 0
  let C : ∀ l : Fin 3, T → Fin n → β l := fun l => match l with
    | ⟨0, _⟩ => fun _ _ => Classical.arbitrary _
    | ⟨1, _⟩ => fun t => D₁ t.1 t.2.1
    | ⟨2, _⟩ => fun t => D₂ t.1 t.2.2
  have e₀₁ : ∀ t, part 0 1 t = (t.1, t.2.1, 0) := fun t => by simp [part]
  have e₀₂ : ∀ t, part 0 2 t = (0, 0, t.2.2) := fun t => by simp [part]
  have e₁₂ : ∀ t, part 1 2 t = (t.1, 0, 0) := fun t => by simp [part]
  have hcard : ∀ j k, Nat.card (Set.range (part j k)) ≤ M j k := fun j k => by
    by_cases h₀₁' : j = 0 ∧ k = 1
    · obtain ⟨rfl, rfl⟩ := h₀₁'
      have h₁ : Nat.card (Set.range (part 0 1)) ≤ Nat.card (Fin Lu × Fin L₁) :=
        Nat.card_le_card_of_injective (fun t => (t.1.1, t.1.2.1)) (by
          rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ h
          refine Subtype.ext ?_
          simp only [e₀₁] at h ⊢
          obtain ⟨a, b⟩ := Prod.mk.inj h
          rw [a, b])
      refine h₁.trans ?_
      rwa [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    by_cases h₀₂' : j = 0 ∧ k = 2
    · obtain ⟨rfl, rfl⟩ := h₀₂'
      have h₁ : Nat.card (Set.range (part 0 2)) ≤ Nat.card (Fin L₂) :=
        Nat.card_le_card_of_injective (fun t => t.1.2.2) (by
          rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ h
          refine Subtype.ext ?_
          simp only [e₀₂] at h ⊢
          rw [h])
      refine h₁.trans ?_
      rwa [Nat.card_eq_fintype_card, Fintype.card_fin]
    by_cases h₁₂' : j = 1 ∧ k = 2
    · obtain ⟨rfl, rfl⟩ := h₁₂'
      have h₁ : Nat.card (Set.range (part 1 2)) ≤ Nat.card (Fin Lu) :=
        Nat.card_le_card_of_injective (fun t => t.1.1) (by
          rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ h
          refine Subtype.ext ?_
          simp only [e₁₂] at h ⊢
          rw [h])
      refine h₁.trans ?_
      rwa [Nat.card_eq_fintype_card, Fintype.card_fin]
    · have h₁ : Nat.card (Set.range (part j k)) ≤ Nat.card Unit :=
        Nat.card_le_card_of_injective (fun _ => ()) (by
          rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ _
          refine Subtype.ext ?_
          simp only [part, ite_eq_right h₀₁', ite_eq_right h₀₂', ite_eq_right h₁₂'])
      simp only [Nat.card_unique] at h₁
      exact h₁.trans (hM j k)
  have hne : Nonempty T := ⟨0⟩
  obtain ⟨c', hc'⟩ := MDNetCode.ofParts (s := (0 : Fin 3)) (M := M) (T := T) (n := n)
    (α := α) (β := β) part know merge (fun x => (fu x, f₁ x, f₂ x)) C hcard
    (fun k t hk => by
      fin_cases k
      · exact absurd rfl hk
      · simp [merge, know, part]
      · simp [merge, know, part])
    (fun k l t hk => by
      fin_cases k
      · exact absurd rfl hk
      · fin_cases l <;> simp [know, part]
      · fin_cases l <;> simp [know, part])
    (fun l t hl => by
      fin_cases l
      · exact absurd rfl hl
      · simp [C, know]
      · simp [C, know])
  exact ⟨c', fun x => hc' x 1 (by decide), fun x => hc' x 2 (by decide)⟩

open Classical in
/-- The expected distortion of codewords that are typical with the source, except with probability
`η`. -/
lemma sum_seqDistortion_le_of_triLaw {Ω υ δ : Type*} [Fintype Ω] [Fintype υ] [Fintype δ]
    [Nonempty δ] {μ : Ω → ℝ} (hμ : IsPMF μ) (hP : IsPMF P) {d' : α → δ → ℝ} (hd : ∀ x y, 0 ≤ d' x y)
    (V : Ω → υ) (X : Ω → α) (Y : Ω → δ) {n : ℕ} (hn : 0 < n) {ε η : ℝ} (hε : 0 ≤ ε)
    (v : (Fin n → α) → Fin n → υ) (y : (Fin n → α) → Fin n → δ)
    (hA : ∑ x, iidPMF P n x * (if zipSeq (zipSeq (v x) x) (y x) ∈
      robustTypicalSet (triLaw μ V X Y) n ε then (0 : ℝ) else 1) ≤ η) :
    ∑ x, iidPMF P n x * seqDistortion d' x (y x) ≤
      (1 + ε) * ∑ ω, μ ω * d' (X ω) (Y ω) + maxDistortion d' * η := by
  classical
  obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hne : Nonempty α := ⟨a₀⟩
  have hp := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := maxDistortion_nonneg hd
  have hE : 0 ≤ ∑ ω, μ ω * d' (X ω) (Y ω) := sum_nonneg fun ω _ =>
    mul_nonneg (hμ.nonneg ω) (hd _ _)
  have hpt : ∀ x, seqDistortion d' x (y x) ≤ (1 + ε) * (∑ ω, μ ω * d' (X ω) (Y ω)) +
      maxDistortion d' * (if zipSeq (zipSeq (v x) x) (y x) ∈
        robustTypicalSet (triLaw μ V X Y) n ε then 0 else 1) := fun x => by
    by_cases hx : zipSeq (zipSeq (v x) x) (y x) ∈ robustTypicalSet (triLaw μ V X Y) n ε
    · rw [ite_eq_left hx, mul_zero, add_zero, seqDistortion, div_le_iff₀ hn']
      have h₁ := sum_le_of_mem_triLaw hμ V X Y d' hd hx
      linarith
    · rw [ite_eq_right hx, mul_one]
      have h₁ := seqDistortion_le_maxDistortion d' hn x (y x)
      have h₂ : 0 ≤ (1 + ε) * ∑ ω, μ ω * d' (X ω) (Y ω) := by positivity
      linarith
  calc ∑ x, iidPMF P n x * seqDistortion d' x (y x)
      ≤ ∑ x, iidPMF P n x * ((1 + ε) * (∑ ω, μ ω * d' (X ω) (Y ω)) +
          maxDistortion d' * (if zipSeq (zipSeq (v x) x) (y x) ∈
          robustTypicalSet (triLaw μ V X Y) n ε then 0 else 1)) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hp.nonneg x)
    _ = (1 + ε) * (∑ ω, μ ω * d' (X ω) (Y ω)) + maxDistortion d' *
          ∑ x, iidPMF P n x * (if zipSeq (zipSeq (v x) x) (y x) ∈
          robustTypicalSet (triLaw μ V X Y) n ε then (0 : ℝ) else 1) := by
        simp only [mul_add, sum_add_distrib]
        congr 1
        · rw [← sum_mul, hp.sum_eq_one, one_mul]
        · rw [mul_sum]
          exact sum_congr rfl fun x _ => by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hA hm)

omit [Fintype α] [∀ l, Fintype (β l)] [∀ l, Nonempty (β l)] in
lemma ite_ge_of_and_left {A B : Prop} [Decidable A] [Decidable (A ∧ B)] :
    (if A then (0 : ℝ) else 1) ≤ if A ∧ B then 0 else 1 := by
  by_cases h : A ∧ B
  · rw [ite_eq_left h.1, ite_eq_left h]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

omit [Fintype α] [∀ l, Fintype (β l)] [∀ l, Nonempty (β l)] in
lemma ite_ge_of_and_right {A B : Prop} [Decidable B] [Decidable (A ∧ B)] :
    (if B then (0 : ℝ) else 1) ≤ if A ∧ B then 0 else 1 := by
  by_cases h : A ∧ B
  · rw [ite_eq_left h.2, ite_eq_left h]
  · rw [ite_eq_right h]
    split_ifs <;> norm_num

/-- Achievability, for given rates of the layers. -/
lemma isAchievableMDN_tri_aux {υ : Type u} [Fintype υ] [Nonempty υ] (hP : IsPMF P)
    (hd : ∀ l x y, 0 ≤ d l x y) {μ : α × υ × β 1 × β 2 → ℝ} (hμ : IsTriLaw P μ)
    {R : Fin 3 → Fin 3 → ℝ} {D : Fin 3 → ℝ} (hR : ∀ j k, 0 ≤ R j k)
    (hR0 : ∀ j k, (j, k) ∉ triEdges → R j k = 0) {ru r₁ r₂ : ℝ}
    (hu : I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.1 ; μ] < ru)
    (h₁ : I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.1 | fun z => z.2.1 ; μ] < r₁)
    (h₂ : I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.2 | fun z => z.2.1 ; μ] < r₂)
    (hs : ∀ᶠ n : ℕ in atTop, ⌈exp ((n : ℝ) * ru)⌉₊ * ⌈exp ((n : ℝ) * r₁)⌉₊ ≤ 2 ^ ⌊(n : ℝ) *
      R 0 1⌋₊ ∧
      ⌈exp ((n : ℝ) * r₂)⌉₊ ≤ 2 ^ ⌊(n : ℝ) * R 0 2⌋₊ ∧
      ⌈exp ((n : ℝ) * ru)⌉₊ ≤ 2 ^ ⌊(n : ℝ) * R 1 2⌋₊)
    (hD₁ : ∑ z, μ z * d 1 z.1 z.2.2.1 ≤ D 1) (hD₂ : ∑ z, μ z * d 2 z.1 z.2.2.2 ≤ D 2) :
    IsAchievableMDN P d 0 triEdges R D := by
  classical
  obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty α := ⟨a₀⟩
  refine ⟨hR, hR0, fun ε hε => ?_⟩
  have hE₁0 : 0 ≤ ∑ z, μ z * d 1 z.1 z.2.2.1 := sum_nonneg fun z _ =>
    mul_nonneg (hμ.isPMF.nonneg z) (hd _ _ _)
  have hE₂0 : 0 ≤ ∑ z, μ z * d 2 z.1 z.2.2.2 := sum_nonneg fun z _ =>
    mul_nonneg (hμ.isPMF.nonneg z) (hd _ _ _)
  have hm₁0 : 0 ≤ maxDistortion (d 1) := maxDistortion_nonneg (hd 1)
  have hm₂0 : 0 ≤ maxDistortion (d 2) := maxDistortion_nonneg (hd 2)
  obtain ⟨Bd, hBd⟩ : ∃ Bd, Bd = (∑ z, μ z * d 1 z.1 z.2.2.1) + (∑ z, μ z * d 2 z.1 z.2.2.2) +
      maxDistortion (d 1) + maxDistortion (d 2) + 1 := ⟨_, rfl⟩
  have hBd0 : 0 < Bd := by linarith
  obtain ⟨εt, hεt⟩ : ∃ εt, εt = ε / (6 * Bd) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = ε / (8 * Bd) := ⟨_, rfl⟩
  have hεt0 : 0 < εt := by
    rw [hεt]
    positivity
  have hη0 : 0 < η := by
    rw [hη]
    positivity
  have hscale : εt * Bd = ε / 6 := by
    rw [hεt]
    field_simp
  have hscale₂ : η * Bd = ε / 8 := by
    rw [hη]
    field_simp
  filter_upwards [exists_tri_cover hμ.isPMF Prod.fst (fun z : α × υ × β 1 × β 2 => z.2.1)
    (fun z => z.2.2.1) (fun z => z.2.2.2) hu h₁ h₂ hεt0 hη0, hs, eventually_gt_atTop 0]
    with n hcov hsn hn0
  obtain ⟨fu, f₁, f₂, Du, D₁, D₂, hsum⟩ := hcov
  rw [hμ.fst] at hsum
  obtain ⟨hs₀₁, hs₀₂, hs₁₂⟩ := hsn
  have hLp : ∀ r : ℝ, 0 < ⌈exp ((n : ℝ) * r)⌉₊ := fun r => Nat.ceil_pos.2 (exp_pos _)
  have hneu : NeZero ⌈exp ((n : ℝ) * ru)⌉₊ := ⟨(hLp ru).ne'⟩
  have hne₁ : NeZero ⌈exp ((n : ℝ) * r₁)⌉₊ := ⟨(hLp r₁).ne'⟩
  have hne₂ : NeZero ⌈exp ((n : ℝ) * r₂)⌉₊ := ⟨(hLp r₂).ne'⟩
  have hMpos : ∀ j k, 0 < (fun j k => 2 ^ ⌊(n : ℝ) * R j k⌋₊ : Fin 3 → Fin 3 → ℕ) j k :=
    fun j k => by positivity
  obtain ⟨c', hc₁, hc₂⟩ := exists_tri_code (α := α) (β := β) hMpos hs₀₁ hs₀₂ hs₁₂ fu f₁ f₂ D₁ D₂
  refine ⟨c', fun l hl => ?_⟩
  have hp := iidPMF_isPMF hP n
  have hsum₁ := (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (ite_ge_of_and_left (A := zipSeq (zipSeq (Du (fu x)) x) (D₁ (fu x) (f₁ x)) ∈
      robustTypicalSet (triLaw μ (fun z : α × υ × β 1 × β 2 => z.2.1) Prod.fst
        (fun z => z.2.2.1)) n εt)
      (B := zipSeq (zipSeq (Du (fu x)) x) (D₂ (fu x) (f₂ x)) ∈
      robustTypicalSet (triLaw μ (fun z : α × υ × β 1 × β 2 => z.2.1) Prod.fst
        (fun z => z.2.2.2)) n εt)) (hp.nonneg x)).trans hsum
  have hsum₂ := (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
    (ite_ge_of_and_right (A := zipSeq (zipSeq (Du (fu x)) x) (D₁ (fu x) (f₁ x)) ∈
      robustTypicalSet (triLaw μ (fun z : α × υ × β 1 × β 2 => z.2.1) Prod.fst
        (fun z => z.2.2.1)) n εt)
      (B := zipSeq (zipSeq (Du (fu x)) x) (D₂ (fu x) (f₂ x)) ∈
      robustTypicalSet (triLaw μ (fun z : α × υ × β 1 × β 2 => z.2.1) Prod.fst
        (fun z => z.2.2.2)) n εt)) (hp.nonneg x)).trans hsum
  have hl₁₂ : l = 1 ∨ l = 2 := by
    revert l
    decide
  rcases hl₁₂ with rfl | rfl
  · have hbd := sum_seqDistortion_le_of_triLaw hμ.isPMF hP (hd 1)
      (fun z : α × υ × β 1 × β 2 => z.2.1) Prod.fst (fun z => z.2.2.1) hn0 hεt0.le
      (fun x => Du (fu x)) (fun x => D₁ (fu x) (f₁ x)) hsum₁
    simp only [MDNetCode.distortion, hc₁]
    refine hbd.trans ?_
    have h₃ : εt * (∑ z, μ z * d 1 z.1 z.2.2.1) ≤ εt * Bd := mul_le_mul_of_nonneg_left
      (by linarith) hεt0.le
    have h₄ : maxDistortion (d 1) * η ≤ Bd * η := mul_le_mul_of_nonneg_right
      (by linarith) hη0.le
    nlinarith
  · have hbd := sum_seqDistortion_le_of_triLaw hμ.isPMF hP (hd 2)
      (fun z : α × υ × β 1 × β 2 => z.2.1) Prod.fst (fun z => z.2.2.2) hn0 hεt0.le
      (fun x => Du (fu x)) (fun x => D₂ (fu x) (f₂ x)) hsum₂
    simp only [MDNetCode.distortion, hc₂]
    refine hbd.trans ?_
    have h₃ : εt * (∑ z, μ z * d 2 z.1 z.2.2.2) ≤ εt * Bd := mul_le_mul_of_nonneg_left
      (by linarith) hεt0.le
    have h₄ : maxDistortion (d 2) * η ≤ Bd * η := mul_le_mul_of_nonneg_right
      (by linarith) hη0.le
    nlinarith

/-- **Pages 21-8 and 21-9 of [elgamal2010]: achievability for the triangular network.** -/
theorem isAchievableMDN_tri {υ : Type u} [Fintype υ] [Nonempty υ] (hP : IsPMF P)
    (hd : ∀ l x y, 0 ≤ d l x y) {μ : α × υ × β 1 × β 2 → ℝ} (hμ : IsTriLaw P μ)
    {R : Fin 3 → Fin 3 → ℝ} {D : Fin 3 → ℝ} (hR : ∀ j k, 0 ≤ R j k)
    (hR0 : ∀ j k, (j, k) ∉ triEdges → R j k = 0)
    (h₁₂ : I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.1 ; μ] < R 1 2 * log 2)
    (h₀₁ : I[Prod.fst : pair (fun z : α × υ × β 1 × β 2 => z.2.2.1) (fun z => z.2.1) ; μ] <
      R 0 1 * log 2)
    (h₀₂ : I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.2 | fun z => z.2.1 ; μ] < R 0 2 * log 2)
    (hD₁ : ∑ z, μ z * d 1 z.1 z.2.2.1 ≤ D 1) (hD₂ : ∑ z, μ z * d 2 z.1 z.2.2.2 ≤ D 2) :
    IsAchievableMDN P d 0 triEdges R D := by
  have hμp := hμ.isPMF
  have hl2 := log_pos one_lt_two
  obtain ⟨Iu, hIu⟩ : ∃ Iu, Iu = I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.1 ; μ] := ⟨_, rfl⟩
  obtain ⟨I₁, hI₁⟩ : ∃ I₁, I₁ = I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.1 |
    fun z => z.2.1 ; μ] := ⟨_, rfl⟩
  obtain ⟨I₂, hI₂⟩ : ∃ I₂, I₂ = I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.2 |
    fun z => z.2.1 ; μ] := ⟨_, rfl⟩
  have hIu0 : 0 ≤ Iu := hIu ▸ mutualInfo_nonneg hμp _ _
  have hI₁0 : 0 ≤ I₁ := hI₁ ▸ condMutualInfo_nonneg hμp _ _ _
  have hI₂0 : 0 ≤ I₂ := hI₂ ▸ condMutualInfo_nonneg hμp _ _ _
  have hchain := chain_rule_mutualInfo₂ hμp (Prod.fst : α × υ × β 1 × β 2 → α)
    (fun z => z.2.2.1) (fun z => z.2.1)
  rw [hchain, ← hIu, ← hI₁] at h₀₁
  rw [← hIu] at h₁₂
  rw [← hI₂] at h₀₂
  obtain ⟨δ, hδ0, h₁₂', h₀₁', h₀₂'⟩ : ∃ δ > 0, Iu + 4 * δ < R 1 2 * log 2 ∧
      Iu + I₁ + 4 * δ < R 0 1 * log 2 ∧ I₂ + 4 * δ < R 0 2 * log 2 := by
    refine ⟨min (min (R 1 2 * log 2 - Iu) (R 0 1 * log 2 - (Iu + I₁))) (R 0 2 * log 2 - I₂) / 8,
      div_pos (lt_min (lt_min ?_ ?_) ?_) (by norm_num), ?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
    · have := (min_le_left (min (R 1 2 * log 2 - Iu) (R 0 1 * log 2 - (Iu + I₁)))
        (R 0 2 * log 2 - I₂)).trans (min_le_left _ _)
      have h₃ : 0 < min (min (R 1 2 * log 2 - Iu) (R 0 1 * log 2 - (Iu + I₁)))
          (R 0 2 * log 2 - I₂) := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      linarith
    · have := (min_le_left (min (R 1 2 * log 2 - Iu) (R 0 1 * log 2 - (Iu + I₁)))
        (R 0 2 * log 2 - I₂)).trans (min_le_right _ _)
      have h₃ : 0 < min (min (R 1 2 * log 2 - Iu) (R 0 1 * log 2 - (Iu + I₁)))
          (R 0 2 * log 2 - I₂) := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      linarith
    · have := min_le_right (min (R 1 2 * log 2 - Iu) (R 0 1 * log 2 - (Iu + I₁)))
        (R 0 2 * log 2 - I₂)
      have h₃ : 0 < min (min (R 1 2 * log 2 - Iu) (R 0 1 * log 2 - (Iu + I₁)))
          (R 0 2 * log 2 - I₂) := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
      linarith
  have hsize : ∀ᶠ n : ℕ in atTop, 4 * log 2 ≤ n * δ :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hδ0).eventually_ge_atTop _
  refine isAchievableMDN_tri_aux hP hd hμ hR hR0 (ru := Iu + δ) (r₁ := I₁ + δ) (r₂ := I₂ + δ)
    (by linarith) (by linarith) (by linarith) ?_ hD₁ hD₂
  filter_upwards [hsize, eventually_gt_atTop 0] with n hns hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hb : ∀ r : ℝ, 0 ≤ r → (⌈exp ((n : ℝ) * r)⌉₊ : ℝ) ≤ exp (log 2 + n * r) := fun r hr =>
    ceil_exp_le (mul_nonneg hn'.le hr)
  have hru := hb (Iu + δ) (by linarith)
  have hr₁ := hb (I₁ + δ) (by linarith)
  have hr₂ := hb (I₂ + δ) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have hb' : ((⌈exp ((n : ℝ) * (Iu + δ))⌉₊ * ⌈exp ((n : ℝ) * (I₁ + δ))⌉₊ : ℕ) : ℝ) ≤
        exp ((n : ℝ) * (R 0 1 * log 2) - log 2) := by
      push_cast
      refine (mul_le_mul hru hr₁ (Nat.cast_nonneg _) (exp_pos _).le).trans ?_
      rw [← exp_add]
      refine exp_le_exp.2 ?_
      have h₃ := mul_le_mul_of_nonneg_left h₀₁'.le hn'.le
      nlinarith
    have h₉ := hb'.trans (exp_le_two_pow_floor n (R 0 1))
    exact_mod_cast h₉
  · have hb' : (⌈exp ((n : ℝ) * (I₂ + δ))⌉₊ : ℝ) ≤ exp ((n : ℝ) * (R 0 2 * log 2) - log 2) := by
      refine hr₂.trans (exp_le_exp.2 ?_)
      have h₃ := mul_le_mul_of_nonneg_left h₀₂'.le hn'.le
      nlinarith
    have h₉ := hb'.trans (exp_le_two_pow_floor n (R 0 2))
    exact_mod_cast h₉
  · have hb' : (⌈exp ((n : ℝ) * (Iu + δ))⌉₊ : ℝ) ≤ exp ((n : ℝ) * (R 1 2 * log 2) - log 2) := by
      refine hru.trans (exp_le_exp.2 ?_)
      have h₃ := mul_le_mul_of_nonneg_left h₁₂'.le hn'.le
      nlinarith
    have h₉ := hb'.trans (exp_le_two_pow_floor n (R 1 2))
    exact_mod_cast h₉

end Achievability

/-! ### The inner bound -/

section Inner

variable [∀ l, Nonempty (β l)] {P : α → ℝ} {d : ∀ l, α → β l → ℝ}

/-- **Theorem 2 of Lecture 21 of [elgamal2010]: the inner bound.** -/
theorem triInner_subset_mdnRegion (hP : IsPMF P) (hd : ∀ l x y, 0 ≤ d l x y) (D : Fin 3 → ℝ) :
    triInner P d D ⊆ mdnRegion P d 0 triEdges D := by
  classical
  rintro R ⟨hR, hR0, υ, _, μ, hμ, h₁₂, h₀₁, h₀₂, hD₁, hD₂⟩
  have hl2 := log_pos one_lt_two
  have hneυ : Nonempty υ := by
    obtain ⟨z⟩ : Nonempty (α × υ × β 1 × β 2) :=
      Fintype.card_pos_iff.1 (card_pos_of_isPMF hμ.isPMF)
    exact ⟨z.2.1⟩
  set Rn : ℕ → Fin 3 → Fin 3 → ℝ := fun t j k =>
    R j k + (if (j, k) ∈ triEdges then 1 / ((t : ℝ) + 1) else 0) with hRn
  have hlim : Tendsto Rn atTop (𝓝 R) := by
    refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun k => ?_
    by_cases hjk : (j, k) ∈ triEdges
    · simp only [hRn, hjk, ite_true]
      simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · simp [hRn, hjk]
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun t => ?_)
  have hp : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
  have hstrict : ∀ {j k : Fin 3} {a : ℝ}, (j, k) ∈ triEdges → a ≤ R j k * log 2 →
      a < Rn t j k * log 2 := fun {j k a} hjk ha => by
    simp only [hRn, hjk, ite_true]
    nlinarith [mul_pos hp hl2]
  refine isAchievableMDN_tri hP hd hμ (fun j k => ?_) (fun j k hjk => ?_)
    (hstrict (by decide) h₁₂) (hstrict (by decide) h₀₁) (hstrict (by decide) h₀₂) hD₁ hD₂
  · simp only [hRn]
    have := hR j k
    split_ifs <;> linarith
  · simp only [hRn, hjk, ite_false, add_zero]
    exact hR0 j k hjk

end Inner

/-! ### The converse -/

section Converse

variable {P : α → ℝ} {d : ∀ l, α → β l → ℝ} {n : ℕ}

/-- The letters of a sequence, with a default value after the end. -/
def pastRV (a₀ : α) (k : ℕ) (x : Fin n → α) : α := if h : k < n then x ⟨k, h⟩ else a₀

omit [Fintype α] in
lemma pastRV_coe (a₀ : α) (i : Fin n) (x : Fin n → α) : pastRV a₀ i x = x i := by
  simp [pastRV]

/-- **Lecture 21, page 21-9.** `H(X_Q | Q, M, X^{Q-1}) = (1 / n) H(Xⁿ | M)`, by the chain rule. -/
theorem condEntropy_mix_past {τ : Type*} [Fintype τ] (hP : IsPMF P) (hn : 0 < n) (a₀ : α)
    (M : (Fin n → α) → τ) :
    H[fun z : (Fin n → α) × Fin n => z.1 z.2 | fun z =>
        (⟨z.2, M z.1, prefixRV (pastRV a₀) z.2 z.1⟩ : Σ i : Fin n, τ × (Fin i → α)) ;
        mixLaw (iidPMF P n) (Fin n)] =
      (n : ℝ)⁻¹ * H[id | M ; iidPMF P n] := by
  classical
  have hμ := iidPMF_isPMF hP n
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := condEntropy_mix hμ (fun (i : Fin n) (x : Fin n → α) => x i)
    (b := fun i : Fin n => τ × (Fin i → α)) fun i => pair M (prefixRV (pastRV a₀) i)
  simp only [Fintype.card_fin] at h
  refine h.trans ?_
  congr 1
  have hc := chain_rule_entropy_cond hμ (pastRV a₀) M n
  have hp : prefixRV (pastRV a₀) n = (id : (Fin n → α) → Fin n → α) := by
    funext x j
    simp only [prefixRV, pastRV_coe, id]
  rw [hp, sum_range] at hc
  rw [hc]
  refine sum_congr rfl fun i _ => ?_
  have hZ : pastRV a₀ (i : ℕ) = fun x : Fin n → α => x i := funext fun x => pastRV_coe a₀ i x
  rw [hZ]

/-- `H(X) - (1 / n) H(Xⁿ | M) ≤ (1 / n) log |𝓜|`. -/
lemma entropy_sub_condEntropy_le {τ : Type*} [Fintype τ] (hP : IsPMF P) (hn : 0 < n)
    (M : (Fin n → α) → τ) :
    entropy P - (n : ℝ)⁻¹ * H[id | M ; iidPMF P n] ≤ (n : ℝ)⁻¹ * log (Fintype.card τ) := by
  have hμ := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h5 : H[id ; iidPMF P n] = n * entropy P := by
    rw [entropyRV, dist_id, entropy_iidPMF hP]
  have h6 : H[id ; iidPMF P n] - H[id | M ; iidPMF P n] ≤ log (Fintype.card τ) := by
    rw [← mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_comm hμ,
      mutualInfo_eq_entropy_sub_condEntropy hμ]
    have a1 := condEntropy_nonneg hμ M (id : (Fin n → α) → _)
    have a2 := entropyRV_le_log_card hμ M
    linarith
  have hx : entropy P = (n : ℝ)⁻¹ * H[id ; iidPMF P n] := by
    rw [h5, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  have hz := mul_le_mul_of_nonneg_left h6 (inv_nonneg.2 hn'.le)
  rw [mul_sub] at hz
  linarith

omit [Fintype α] [∀ l, Fintype (β l)] in
/-- A function that is determined by another one factors through it. -/
lemma exists_factor {A B C : Type*} [Nonempty C] {f : A → B} {g : A → C}
    (h : ∀ a a', f a = f a' → g a = g a') : ∃ G : B → C, ∀ a, g a = G (f a) := by
  classical
  refine ⟨fun b => if h' : ∃ a, f a = b then g h'.choose else Classical.arbitrary C, fun a => ?_⟩
  have h' : ∃ a', f a' = f a := ⟨a, rfl⟩
  simp only [h', ↓reduceDIte]
  exact h _ _ h'.choose_spec.symm

/-- Entropies under a pushforward. -/
lemma condEntropy_dist {Ω T a b : Type*} [Fintype Ω] [Fintype T] [Fintype a] [Fintype b]
    {ν : Ω → ℝ} (hν : IsPMF ν) (W : Ω → T) (A : T → a) (B : T → b) :
    H[A | B ; dist ν W] = H[A ∘ W | B ∘ W ; ν] :=
  condEntropy_eq_of_dist_pair_eq (hν.dist W) hν (dist_comp_eq ν W (pair B A)).symm

/-- **Pages 21-9 and 21-10 of [elgamal2010]: the converse for one code.** -/
theorem MDNetCode.exists_tri_law [Nonempty (β 1)] [Nonempty (β 2)] {M : Fin 3 → Fin 3 → ℕ}
    [∀ j k, NeZero (M j k)] (c : MDNetCode (0 : Fin 3) M n α β) (hP : IsPMF P) (hn : 0 < n) :
    ∃ (υ : Type u) (_ : Fintype υ) (μ : α × υ × β 1 × β 2 → ℝ), IsTriLaw P μ ∧
      I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.1 ; μ] ≤ (n : ℝ)⁻¹ * log (M 1 2) ∧
      I[Prod.fst : pair (fun z : α × υ × β 1 × β 2 => z.2.2.1) (fun z => z.2.1) ; μ] ≤
        (n : ℝ)⁻¹ * log (M 0 1) ∧
      I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.2 | fun z => z.2.1 ; μ] ≤
        (n : ℝ)⁻¹ * log (M 0 2) ∧
      ∑ z, μ z * d 1 z.1 z.2.2.1 = c.distortion P d 1 ∧
      ∑ z, μ z * d 2 z.1 z.2.2.2 = c.distortion P d 2 := by
  classical
  obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnF : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  set ν := mixLaw (iidPMF P n) (Fin n) with hνd
  set M₀₁ : (Fin n → α) → Fin (M 0 1) := fun x => c.edge x 0 1 with hM₀₁
  set M₀₂ : (Fin n → α) → Fin (M 0 2) := fun x => c.edge x 0 2 with hM₀₂
  set M₁₂ : (Fin n → α) → Fin (M 1 2) := fun x => c.edge x 1 2 with hM₁₂
  -- the functions of the indices
  have hne₁₂ : Nonempty (Fin (M 1 2)) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin (M 0 1) → Fin (M 1 2), ∀ x, M₁₂ x = g (M₀₁ x) := by
    refine exists_factor fun x x' h => ?_
    simp only [hM₁₂]
    rw [c.edge_eq x, c.edge_eq x', c.relay 1 2 _ x x' (by decide)]
    congr 1
    funext j hj
    have hj0 : j = 0 := by
      revert j
      decide
    subst hj0
    exact h
  have hneo₁ : Nonempty (Fin n → β 1) := ⟨fun _ => Classical.arbitrary _⟩
  have hneo₂ : Nonempty (Fin n → β 2) := ⟨fun _ => Classical.arbitrary _⟩
  obtain ⟨o₁, ho₁⟩ : ∃ o₁ : Fin (M 0 1) → Fin n → β 1, ∀ x, c.out x 1 = o₁ (M₀₁ x) := by
    refine exists_factor fun x x' h => ?_
    simp only [MDNetCode.out]
    congr 1
    funext j hj
    have hj0 : j = 0 := by
      revert j
      decide
    subst hj0
    exact h
  obtain ⟨o₂, ho₂⟩ : ∃ o₂ : Fin (M 0 2) × Fin (M 1 2) → Fin n → β 2,
      ∀ x, c.out x 2 = o₂ (pair M₀₂ M₁₂ x) := by
    refine exists_factor fun x x' h => ?_
    simp only [MDNetCode.out]
    congr 1
    funext j hj
    have hj' : j = 0 ∨ j = 1 := by
      revert j
      decide
    rcases hj' with rfl | rfl
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).2
  -- the law
  set U : (Fin n → α) × Fin n → Σ i : Fin n, Fin (M 1 2) × (Fin i → α) := fun z =>
    ⟨z.2, M₁₂ z.1, prefixRV (pastRV a₀) z.2 z.1⟩ with hU
  set Xq : (Fin n → α) × Fin n → α := fun z => z.1 z.2 with hXq
  set W : (Fin n → α) × Fin n → α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) × β 1 × β 2 :=
    fun z => (Xq z, U z, c.out z.1 1 z.2, c.out z.1 2 z.2) with hW
  have hentropy : H[Xq ; ν] = entropy P := by
    rw [entropyRV, hXq]
    rw [dist_mix_coord hP hn]
  have hcost : ∀ f : α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) × β 1 × β 2 → ℝ,
      ∑ z, dist ν W z * f z = ∑ z, ν z * f (W z) := fun f => sum_dist_mul ν W f
  refine ⟨_, inferInstance, dist ν W, ⟨hν.dist W, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← dist_comp_eq]
    exact dist_mix_coord hP hn
  · -- `I(U; X)`
    rw [← mutualInfo_comp W, mutualInfo_eq_entropy_sub_condEntropy hν]
    have e₁ : H[Prod.fst ∘ W ; ν] = entropy P := hentropy
    rw [e₁]
    have e₂ : H[Prod.fst ∘ W | (fun z => z.2.1) ∘ W ; ν] = (n : ℝ)⁻¹ * H[id | M₁₂ ; iidPMF P n] :=
      condEntropy_mix_past hP hn a₀ M₁₂
    rw [e₂]
    have := entropy_sub_condEntropy_le hP hn M₁₂
    rwa [Fintype.card_fin] at this
  · -- `I(U, X̂₁; X)`
    rw [← mutualInfo_comp W, mutualInfo_eq_entropy_sub_condEntropy hν]
    have e₁ : H[Prod.fst ∘ W ; ν] = entropy P := hentropy
    rw [e₁]
    have h₁ := condEntropy_le_condEntropy_comp hν Xq
      (fun z : (Fin n → α) × Fin n =>
        (⟨z.2, M₀₁ z.1, prefixRV (pastRV a₀) z.2 z.1⟩ : Σ i : Fin n, Fin (M 0 1) × (Fin i → α)))
      (fun s => (o₁ s.2.1 s.1, (⟨s.1, g s.2.1, s.2.2⟩ : Σ i : Fin n, Fin (M 1 2) × (Fin i → α))))
    have e₂ : (fun s : Σ i : Fin n, Fin (M 0 1) × (Fin i → α) =>
        (o₁ s.2.1 s.1, (⟨s.1, g s.2.1, s.2.2⟩ : Σ i : Fin n, Fin (M 1 2) × (Fin i → α)))) ∘
        (fun z : (Fin n → α) × Fin n =>
          (⟨z.2, M₀₁ z.1, prefixRV (pastRV a₀) z.2 z.1⟩ : Σ i : Fin n, Fin (M 0 1) × (Fin i → α))) =
        (pair (fun z : α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) × β 1 × β 2 => z.2.2.1)
          (fun z => z.2.1)) ∘ W := by
      funext z
      simp only [Function.comp, pair, hW, hU, ho₁, hg]
    rw [e₂, condEntropy_mix_past hP hn a₀ M₀₁] at h₁
    have h₂ := entropy_sub_condEntropy_le hP hn M₀₁
    rw [Fintype.card_fin] at h₂
    have e₃ : H[Prod.fst ∘ W | (pair (fun z : α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) ×
        β 1 × β 2 => z.2.2.1) (fun z => z.2.1)) ∘ W ; ν] = H[Xq | (pair (fun z : α ×
        (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) × β 1 × β 2 => z.2.2.1) (fun z => z.2.1)) ∘ W ;
        ν] := rfl
    rw [e₃]
    linarith
  · -- `I(X̂₂; X | U)`
    rw [condMutualInfo, condEntropy_dist hν W, condEntropy_dist hν W]
    have e₂ : H[Prod.fst ∘ W | (fun z => z.2.1) ∘ W ; ν] = (n : ℝ)⁻¹ * H[id | M₁₂ ; iidPMF P n] :=
      condEntropy_mix_past hP hn a₀ M₁₂
    rw [e₂]
    have h₁ := condEntropy_le_condEntropy_comp hν Xq
      (fun z : (Fin n → α) × Fin n =>
        (⟨z.2, pair M₀₂ M₁₂ z.1, prefixRV (pastRV a₀) z.2 z.1⟩ :
          Σ i : Fin n, (Fin (M 0 2) × Fin (M 1 2)) × (Fin i → α)))
      (fun s => (o₂ s.2.1 s.1, (⟨s.1, s.2.1.2, s.2.2⟩ : Σ i : Fin n, Fin (M 1 2) × (Fin i → α))))
    have e₃ : (fun s : Σ i : Fin n, (Fin (M 0 2) × Fin (M 1 2)) × (Fin i → α) =>
        (o₂ s.2.1 s.1, (⟨s.1, s.2.1.2, s.2.2⟩ : Σ i : Fin n, Fin (M 1 2) × (Fin i → α)))) ∘
        (fun z : (Fin n → α) × Fin n =>
          (⟨z.2, pair M₀₂ M₁₂ z.1, prefixRV (pastRV a₀) z.2 z.1⟩ :
            Σ i : Fin n, (Fin (M 0 2) × Fin (M 1 2)) × (Fin i → α))) =
        (pair (fun z : α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) × β 1 × β 2 => z.2.2.2)
          (fun z => z.2.1)) ∘ W := by
      funext z
      simp only [Function.comp, pair, hW, hU, ho₂]
    rw [e₃, condEntropy_mix_past hP hn a₀ (pair M₀₂ M₁₂)] at h₁
    have h₂ := condEntropy_sub_condEntropy_le (iidPMF_isPMF hP n)
      (id : (Fin n → α) → Fin n → α) M₀₂ M₁₂
    have h₃ := mul_le_mul_of_nonneg_left h₂ (inv_nonneg.2 hn'.le)
    rw [mul_sub] at h₃
    have e₄ : H[Prod.fst ∘ W | (pair (fun z : α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) ×
        β 1 × β 2 => z.2.2.2) (fun z => z.2.1)) ∘ W ; ν] = H[Xq | (pair (fun z : α ×
        (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) × β 1 × β 2 => z.2.2.2) (fun z => z.2.1)) ∘ W ;
        ν] := rfl
    have e₅ : (pair (fun z : α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) × β 1 × β 2 => z.2.2.2)
        (fun z => z.2.1)) ∘ W = pair (fun z : α × (Σ i : Fin n, Fin (M 1 2) × (Fin i → α)) ×
        β 1 × β 2 => z.2.2.2) (fun z => z.2.1) ∘ W := rfl
    linarith
  · rw [hcost]
    exact sum_mix_mul hn fun x i => d 1 (x i) (c.out x 1 i)
  · rw [hcost]
    exact sum_mix_mul hn fun x i => d 2 (x i) (c.out x 2 i)

/-- **Theorem 2 of Lecture 21 of [elgamal2010], the converse.** A rate tuple of the rate–distortion
region satisfies the bounds up to `ε`. The notes state no bound on the alphabet of `U`, so that the
union of the regions over the alphabets is not known to be closed. -/
theorem exists_triInner_of_mem_mdnRegion [Nonempty (β 1)] [Nonempty (β 2)] (hP : IsPMF P)
    {D : Fin 3 → ℝ} {R : Fin 3 → Fin 3 → ℝ} (h : R ∈ mdnRegion P d 0 triEdges D) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ (υ : Type u) (_ : Fintype υ) (μ : α × υ × β 1 × β 2 → ℝ), IsTriLaw P μ ∧
      I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.1 ; μ] ≤ (R 1 2 + ε) * log 2 ∧
      I[Prod.fst : pair (fun z : α × υ × β 1 × β 2 => z.2.2.1) (fun z => z.2.1) ; μ] ≤
        (R 0 1 + ε) * log 2 ∧
      I[Prod.fst : fun z : α × υ × β 1 × β 2 => z.2.2.2 | fun z => z.2.1 ; μ] ≤
        (R 0 2 + ε) * log 2 ∧
      ∑ z, μ z * d 1 z.1 z.2.2.1 ≤ D 1 + ε ∧ ∑ z, μ z * d 2 z.1 z.2.2.2 ≤ D 2 + ε := by
  have hl2 := log_pos one_lt_two
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 h ε hε
  obtain ⟨hb0, -, hc⟩ := hb
  obtain ⟨n, ⟨c, hd⟩, hn⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hclose : ∀ j k, b j k ≤ R j k + ε := fun j k => by
    have h₁ : Dist.dist (b j k) (R j k) ≤ Dist.dist b R :=
      (dist_le_pi_dist (b j) (R j) k).trans (dist_le_pi_dist b R j)
    rw [dist_comm b R, Real.dist_eq] at h₁
    have h₂ := (abs_le.1 h₁).2
    linarith
  have hne : ∀ j k, NeZero (2 ^ ⌊(n : ℝ) * b j k⌋₊) := fun j k => ⟨by positivity⟩
  obtain ⟨υ, hυ, μ, hμ, a₁, a₂, a₃, a₄, a₅⟩ := c.exists_tri_law (d := d) hP hn
  have hrate : ∀ j k, (n : ℝ)⁻¹ * log ((2 ^ ⌊(n : ℝ) * b j k⌋₊ : ℕ) : ℝ) ≤ (R j k + ε) * log 2 :=
    fun j k => by
      rw [inv_mul_le_iff₀ hn']
      refine (log_two_pow_floor_le n (hb0 j k)).trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hclose j k) hl2.le) hn'.le
  refine ⟨υ, hυ, μ, hμ, a₁.trans (hrate 1 2), a₂.trans (hrate 0 1), a₃.trans (hrate 0 2), ?_, ?_⟩
  · rw [a₄]
    exact hd 1 (by decide)
  · rw [a₅]
    exact hd 2 (by decide)

end Converse

end InfoTheory
