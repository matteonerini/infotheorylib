/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACConverse

/-!
# Discrete channels and memorylessness

A discrete channel can be given by a transition matrix `p(y|x)`, or by a function `α(x, z)` of the
input and of a noise variable `Z` independent of the input. A discrete memoryless channel is used
at times `i = 1, 2, …`, and its output at time `i` depends on everything generated before only
through the input `Xᵢ`: `Pr{Yᵢ = y, Xᵢ = x, T = t} = Pr{Xᵢ = x, T = t} p(y|x)`, where `T` stands for
the random variables generated before `Xᵢ`.

## Main definitions

* `noiseChannel a ν`: the transition matrix `Pr{a(x, Z) = y}` of the channel `(a, Z)` with noise
  law `ν`.
* `IsEquivalentChannel W a ν`: the channels `W` and `(a, Z)` are equivalent, (7.34).
* `IsMemorylessUse μ T X Y W`: the use of the channel `W` with input `X` and output `Y` is
  memoryless with respect to the past `T`, (7.35).

## Main statements

* `isEquivalentChannel_coord`: every channel has a noise form, (7.25)–(7.32).
* `IsMemorylessUse.markovChain`: memorylessness gives the Markov chain `T → X → Y`, (7.38).
* `isMemorylessUse_noise`: a channel `(a, Z)` with noise independent of the input and of the past
  is used memorylessly, (7.40)–(7.51).
* `mutualInfo_codeLaw_le_sum`: `I(X; Y) ≤ ∑ᵢ I(Xᵢ; Yᵢ)` without feedback.
* `fbLaw_isMemorylessUse`, `markovChain_fbLaw`: with feedback, `(W, Yⁱ⁻¹) → Xᵢ → Yᵢ`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Sections 7.1, 7.3 and 7.6
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω τ ζ α β : Type*} [Fintype Ω] [Fintype τ] [Fintype ζ] [Fintype α] [Fintype β]

/-! ### Noise forms of a channel -/

/-- **Definition 7.2.** The transition matrix `p(y|x) = Pr{a(x, Z) = y}` of the discrete channel
`(a, Z)`, whose output is `Y = a(X, Z)` with noise `Z ∼ ν` independent of the input. -/
def noiseChannel (a : α → ζ → β) (ν : ζ → ℝ) : α → β → ℝ := fun x => dist ν (a x)

omit [Fintype α] in
lemma noiseChannel_isChannel {a : α → ζ → β} {ν : ζ → ℝ} (hν : IsPMF ν) :
    IsChannel (noiseChannel a ν) := fun x => hν.dist (a x)

/-- **Definition 7.3.** The channels `p(y|x)` and `(a, Z)` are equivalent if
`Pr{a(x, Z) = y} = p(y|x)`, (7.34). -/
def IsEquivalentChannel (W : α → β → ℝ) (a : α → ζ → β) (ν : ζ → ℝ) : Prop :=
  ∀ x y, dist ν (a x) y = W x y

open Classical in
/-- The `i`-th marginal of a product of pmfs. -/
lemma sum_ite_prod_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → β → ℝ}
    (hP : ∀ i, IsPMF (P i)) (i : ι) (b : β) :
    ∑ y : ι → β, (if y i = b then ∏ k, P k (y k) else 0) = P i b := by
  classical
  set φ : ι → β → ℝ := fun k c => if k = i then (if c = b then P k c else 0) else P k c
  have h₁ : ∀ y : ι → β, (if y i = b then ∏ k, P k (y k) else 0) = ∏ k, φ k (y k) := by
    intro y
    by_cases hy : y i = b
    · simp only [hy, ↓reduceIte]
      exact prod_congr rfl fun k _ => by
        by_cases hk : k = i
        · subst hk; simp [φ, hy]
        · simp [φ, hk]
    · simp only [hy, ↓reduceIte]
      exact (prod_eq_zero (mem_univ i) (by simp [φ, hy])).symm
  rw [sum_congr rfl fun y _ => h₁ y, ← Fintype.prod_sum φ]
  rw [prod_eq_single i (fun k _ hk => by simp [φ, hk, (hP k).sum_eq_one]) (by simp)]
  simp [φ]

/-- **(7.25)–(7.32)** Every channel has a noise form: with independent noise variables
`Z_x ∼ p(·|x)`, one for each input `x`, the output `Y = Z_X` gives the channel `p(y|x)`. -/
theorem isEquivalentChannel_coord [DecidableEq α] {W : α → β → ℝ} (hW : IsChannel W) :
    IsEquivalentChannel W (fun x (z : α → β) => z x) (fun z => ∏ x, W x (z x)) := by
  classical
  intro x y
  rw [dist]
  exact sum_ite_prod_apply hW x y

/-! ### Memoryless use of a channel -/

/-- **(7.35)** The use of the channel `W` with input `X` and output `Y` is memoryless with respect
to the past `T`: `Pr{Y = y, X = x, T = t} = Pr{X = x, T = t} p(y|x)`. -/
def IsMemorylessUse (μ : Ω → ℝ) (T : Ω → τ) (X : Ω → α) (Y : Ω → β) (W : α → β → ℝ) : Prop :=
  ∀ t x y, dist μ (pair (pair T X) Y) ((t, x), y) = dist μ (pair T X) (t, x) * W x y

omit [Fintype τ] [Fintype α] [Fintype β] in
lemma dist_pair_pair_assoc (μ : Ω → ℝ) (T : Ω → τ) (X : Ω → α) (Y : Ω → β) (t : τ) (x : α)
    (y : β) : dist μ (pair T (pair X Y)) (t, x, y) = dist μ (pair (pair T X) Y) ((t, x), y) := by
  classical
  simp only [dist, pair_apply, Prod.mk.injEq, and_assoc]

omit [Fintype τ] [Fintype α] [Fintype β] in
/-- **(7.38)** A memoryless use of a channel gives the Markov chain `T → X → Y`. -/
theorem IsMemorylessUse.markovChain [Finite τ] {μ : Ω → ℝ} (hμ : IsPMF μ) {T : Ω → τ}
    {X : Ω → α} {Y : Ω → β} {W : α → β → ℝ} (h : IsMemorylessUse μ T X Y W) :
    MarkovChain μ T X Y := by
  have := Fintype.ofFinite τ
  rw [markovChain_iff_mul hμ]
  intro t x y
  have h₁ : dist μ (pair X Y) (x, y) = dist μ X x * W x y := by
    rw [← sum_dist_pair_left μ T (pair X Y) (x, y)]
    simp only [dist_pair_pair_assoc]
    rw [sum_congr rfl fun t' _ => h t' x y, ← sum_mul, sum_dist_pair_left]
  rw [dist_pair_pair_assoc, h t x y, h₁]
  ring

omit [Fintype τ] [Fintype α] [Fintype β] in
/-- **Definition 7.5, (7.40)–(7.51).** If the output is `Y = a(X, Z)`, where the noise `Z ∼ ν` is
independent of the input and of the past `(T, X)`, the channel `p(y|x) = Pr{a(x, Z) = y}` is used
memorylessly. -/
theorem isMemorylessUse_noise [Finite τ] [Finite α] {μ : Ω → ℝ} {T : Ω → τ} {X : Ω → α}
    {Z : Ω → ζ} {a : α → ζ → β}
    (hZ : IndepRV μ (pair T X) Z) :
    IsMemorylessUse μ T X (fun ω => a (X ω) (Z ω)) (noiseChannel a (dist μ Z)) := by
  classical
  have := Fintype.ofFinite τ
  have := Fintype.ofFinite α
  intro t x y
  set V := pair (pair T X) Z
  have key : dist μ (pair (pair T X) fun ω => a (X ω) (Z ω)) ((t, x), y) =
      ∑ v, dist μ V v * (if v.1 = (t, x) ∧ a v.1.2 v.2 = y then 1 else 0) := by
    rw [sum_dist_mul]
    simp only [dist, V, pair_apply]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h : T ω = t ∧ X ω = x
    · obtain ⟨h₁, h₂⟩ := h
      simp [h₁, h₂]
    · have h' : ¬(T ω, X ω) = (t, x) := fun h'' => h (Prod.ext_iff.1 h'')
      simp only [Prod.mk.injEq] at h'
      simp [h']
  rw [key, Fintype.sum_prod_type, sum_eq_single (t, x)]
  · have e : ∀ z, dist μ (pair (pair T X) Z) ((t, x), z) = dist μ (pair T X) (t, x) * dist μ Z z :=
      fun z => hZ (t, x) z
    have e₂ : dist (dist μ Z) (a x) y = ∑ z, if a x z = y then dist μ Z z else 0 := by
      rw [dist]
    simp only [V, true_and, mul_ite, mul_one, mul_zero, e, noiseChannel]
    rw [e₂, mul_sum]
    refine sum_congr rfl fun z _ => ?_
    by_cases h : a x z = y <;> simp [h]
  · intro v _ hv
    simp [hv]
  · simp

/-! ### Lemma 7.16 -/

/-- **Lemma 7.16, (7.114)–(7.119).** For a discrete memoryless channel used without feedback, with
any input law `P` on `𝒳ⁿ`, `I(X; Y) ≤ ∑ᵢ I(Xᵢ; Yᵢ)`. -/
theorem mutualInfo_codeLaw_le_sum {n : ℕ} {P : (Fin n → α) → ℝ} (hP : IsPMF P) {W : α → β → ℝ}
    (hW : IsChannel W) :
    I[Prod.fst : Prod.snd ; codeLaw P W id] ≤
      ∑ i, I[fun z => z.1 i : fun z => z.2 i ; codeLaw P W id] := by
  have hμ := codeLaw_isPMF (x := id) hP hW
  have h₁ := condEntropy_codeLaw (ν := P) (x := id) hW
  have h₂ : H[Prod.snd ; codeLaw P W id] ≤ ∑ i, H[fun z => z.2 i ; codeLaw P W id] := by
    have := condEntropy_pi_le_sum hμ Prod.snd (fun _ => ())
    simpa only [condEntropy_const hμ] using this
  rw [mutualInfo_eq_entropy_sub_condEntropy' hμ, h₁]
  simp only [id]
  rw [sum_congr rfl fun i _ => mutualInfo_eq_entropy_sub_condEntropy' hμ _ _, sum_sub_distrib]
  linarith

/-! ### Feedback -/

variable {𝒲 : Type*} [Fintype 𝒲] {ν : 𝒲 → ℝ} {W : α → β → ℝ} {enc : ∀ k, 𝒲 → (Fin k → β) → α}

omit [Fintype α] in
/-- **(7.209)** With feedback, the `(k + 1)`-th use of the channel is memoryless with respect to the
past `(W, Yᵏ)`, which determines the input `X_{k+1} = enc k W Yᵏ`. -/
theorem fbLaw_isMemorylessUse (hW : IsChannel W) (k : ℕ) :
    IsMemorylessUse (fbLaw ν W enc (k + 1)) (fun z => (z.1, Fin.init z.2))
      (fun z => enc k z.1 (Fin.init z.2)) (fun z => z.2 (Fin.last k)) W := by
  classical
  rintro ⟨w, u⟩ x y
  have hT : dist (fbLaw ν W enc (k + 1)) (fun z => (z.1, Fin.init z.2)) (w, u) =
      fbLaw ν W enc k (w, u) := by rw [dist_fbLaw_init hW k]
  -- Both sides vanish unless `x` is the input `enc k w u`.
  have hTX : dist (fbLaw ν W enc (k + 1))
      (pair (fun z => (z.1, Fin.init z.2)) fun z => enc k z.1 (Fin.init z.2)) ((w, u), x) =
        if x = enc k w u then fbLaw ν W enc k (w, u) else 0 := by
    rw [← hT]
    split_ifs with hx
    · simp only [dist, pair_apply, Prod.mk.injEq]
      refine sum_congr rfl fun z _ => ?_
      by_cases hz : z.1 = w ∧ Fin.init z.2 = u
      · obtain ⟨h₁, h₂⟩ := hz
        simp [h₁, h₂, hx]
      · simp only [hz, false_and, ↓reduceIte]
    · simp only [dist, pair_apply, Prod.mk.injEq]
      exact sum_eq_zero fun z _ => ite_eq_right_iff.2 fun h => absurd
        (by rw [← h.2, h.1.1, h.1.2]) hx
  rw [hTX]
  split_ifs with hx
  · simp only [dist, pair_apply, Prod.mk.injEq]
    rw [sum_eq_single (w, Fin.snoc u y)]
    · simp [hx, fbLaw_snoc]
    · rintro ⟨w', v⟩ _ hne
      refine ite_eq_right_iff.2 fun h => absurd ?_ hne
      obtain ⟨⟨⟨h₁, h₂⟩, -⟩, h₃⟩ := h
      simp only at h₁ h₂ h₃
      subst h₁
      rw [← h₂, ← h₃, Fin.snoc_init_self]
    · simp
  · simp only [dist, pair_apply, Prod.mk.injEq, zero_mul]
    exact sum_eq_zero fun z _ => ite_eq_right_iff.2 fun h => absurd
      (by rw [← h.1.2, h.1.1.1, h.1.1.2]) hx

omit [Fintype α] in
/-- **Lemma 7.22.** With feedback, `(W, Yⁱ⁻¹) → Xᵢ → Yᵢ` is a Markov chain, (7.210). -/
theorem markovChain_fbLaw (hν : IsPMF ν) (hW : IsChannel W) (k : ℕ) :
    MarkovChain (fbLaw ν W enc (k + 1)) (fun z => (z.1, Fin.init z.2))
      (fun z => enc k z.1 (Fin.init z.2)) (fun z => z.2 (Fin.last k)) :=
  (fbLaw_isMemorylessUse hW k).markovChain (fbLaw_isPMF hν hW (k + 1))

end InfoTheory
