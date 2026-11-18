/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCSuperpositionLaws

/-!
# The superposition coding inner bound

Theorem 1 of Lecture 5 of El Gamal and Kim: a rate pair `(R₁, R₂)`, in bits, is achievable for the
DM-BC `p(y₁, y₂ | x)` if `R₁ < I(X; Y₁ | U)`, `R₂ < I(U; Y₂)` and `R₁ + R₂ < I(X; Y₁)` for some
`p(u, x)`. The random codebook has independent cloud centers `uⁿ(m₂)`, drawn i.i.d. from `p(u)`,
and for each of them conditionally independent satellite codewords `xⁿ(m₁, m₂)`, drawn from
`∏ᵢ p(xᵢ | uᵢ(m₂))`. Receiver 2 decodes the cloud center and receiver 1 the satellite codeword.

We use the weak typicality of Chapter 7 of Cover and Thomas. The law of one column
`(uⁿ, xⁿ(1), …, xⁿ(L))` of the codebook is `superpositionColumnLaw`, and the codebook is an i.i.d.
family of columns, so the averages over codebooks reduce to the lemmas on `iidPMF`. The event `E₁₂`
is not an instance of Theorem 7.6.1, as the wrong satellite codeword is only conditionally
independent of the output given the cloud center. We bound it directly on the typical triples:
`p(uⁿ) p(x'ⁿ | uⁿ) p(yⁿ | uⁿ) = p(uⁿ, x'ⁿ) p(uⁿ, yⁿ) / p(uⁿ)`, so that the set
`superpositionTypicalSet` also asks for `uⁿ` and `(uⁿ, yⁿ)` to be typical.

The results are stated for a channel `V` from `X` to the receiver considered, so that they apply to
both `p(y₁ | x)` and `p(y₂ | x)`, and also give the region with the roles of the receivers
exchanged.

## Main definitions

* `superpositionDecode T C d`: the decoder of the satellite message.

## Main statements

* `sum_superposition_atyp_le`, `sum_superposition_satellite_le`,
  `sum_superposition_wrongCloud_le`: the events `E₁₁`, `E₁₂`, `E₁₃` of the notes.
* `sum_superposition_cloudAtyp_eq`, `sum_superposition_cloudWrong_le`: the events `E₂₁`, `E₂₂`.
  These five are in `Network.BCSuperpositionLaws`.
* `sum_codebook_superpositionDecode_le`, `sum_codebook_superpositionCloudDecode_le`: the
  probabilities of error of the two decoders, averaged over the random codebooks.
* `exists_bcCode_superposition`, `exists_bcCode_superposition₂`: some code does at least this well.
* `superpositionRegionBits_subset`: **Theorem 1 of Lecture 5**, the superposition coding inner
  bound.
* `superpositionRegionBits₂_subset`: the inner bound with the roles of the receivers exchanged.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {𝒰 α β : Type*} [Fintype 𝒰] [Fintype α] [Fintype β]
variable {q : 𝒰 × α → ℝ} {V : α → β → ℝ}

/-! ### Superposition decoding -/

open Classical in
/-- **Lecture 5.** Decoding of the satellite message: declare `l` if it is the unique message
such that `(uⁿ(k), xⁿ(l, k), yⁿ) ∈ T` for some cloud message `k`, and `d` otherwise. The codebook
`C` has the cloud centers `(C k).1` and the satellite codewords `(C k).2 l`. -/
def superpositionDecode {n K L : ℕ} (T : Finset ((Fin n → 𝒰) × (Fin n → α) × (Fin n → β)))
    (C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)) (d : Fin L) (y : Fin n → β) : Fin L :=
  if h : ∃ l, (∃ k, ((C k).1, (C k).2 l, y) ∈ T) ∧
      ∀ l', (∃ k, ((C k).1, (C k).2 l', y) ∈ T) → l' = l then h.choose else d

omit [Fintype 𝒰] [Fintype α] [Fintype β] in
lemma superpositionDecode_eq {n K L : ℕ} {T : Finset ((Fin n → 𝒰) × (Fin n → α) × (Fin n → β))}
    {C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)} (d : Fin L) {y : Fin n → β} {l : Fin L}
    (hl : ∃ k, ((C k).1, (C k).2 l, y) ∈ T)
    (huniq : ∀ l', (∃ k, ((C k).1, (C k).2 l', y) ∈ T) → l' = l) :
    superpositionDecode T C d y = l := by
  have h : ∃ l, (∃ k, ((C k).1, (C k).2 l, y) ∈ T) ∧
      ∀ l', (∃ k, ((C k).1, (C k).2 l', y) ∈ T) → l' = l := ⟨l, hl, huniq⟩
  unfold superpositionDecode
  split
  · next h' => exact huniq _ h'.choose_spec.1
  · next h' => exact absurd h h'

omit [Fintype 𝒰] [Fintype α] [Fintype β] in
open Classical in
/-- **Lecture 5.** A satellite decoding error for the message pair `(l, k)` occurs only if the
triple sent is not typical (`E₁₁`), a wrong satellite codeword of the right cloud center is typical
(`E₁₂`), or a wrong satellite codeword of a wrong cloud center is typical (`E₁₃`). -/
lemma superpositionDecode_ne_le {n K L : ℕ}
    (T : Finset ((Fin n → 𝒰) × (Fin n → α) × (Fin n → β)))
    (C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)) (d : Fin L) (y : Fin n → β) (k : Fin K)
    (l : Fin L) :
    (if superpositionDecode T C d y ≠ l then (1 : ℝ) else 0) ≤
      (if ((C k).1, (C k).2 l, y) ∈ T then 0 else 1) +
        ∑ l' ∈ univ.erase l, (if ((C k).1, (C k).2 l', y) ∈ T then 1 else 0) +
        ∑ k' ∈ univ.erase k, ∑ l' ∈ univ.erase l,
          (if ((C k').1, (C k').2 l', y) ∈ T then 1 else 0) := by
  have hind : ∀ t : (Fin n → 𝒰) × (Fin n → α) × (Fin n → β),
      0 ≤ (if t ∈ T then (1 : ℝ) else 0) := fun t => by split_ifs <;> norm_num
  have hS₁ := sum_nonneg fun l' (_ : l' ∈ univ.erase l) => hind ((C k).1, (C k).2 l', y)
  have hS₂ := sum_nonneg fun k' (_ : k' ∈ univ.erase k) =>
    sum_nonneg fun l' (_ : l' ∈ univ.erase l) => hind ((C k').1, (C k').2 l', y)
  have h0 : 0 ≤ (if ((C k).1, (C k).2 l, y) ∈ T then (0 : ℝ) else 1) := by split_ifs <;> norm_num
  by_cases hd : superpositionDecode T C d y = l
  · simp only [hd, ne_eq, not_true_eq_false, ↓reduceIte]
    linarith
  simp only [hd, ne_eq, not_false_eq_true, ↓reduceIte]
  by_cases hw : ((C k).1, (C k).2 l, y) ∈ T
  swap
  · simp only [hw, ↓reduceIte]
    linarith
  obtain ⟨l', ⟨k', hk'⟩, hne⟩ : ∃ l', (∃ k', ((C k').1, (C k').2 l', y) ∈ T) ∧ l' ≠ l := by
    by_contra hne
    push Not at hne
    exact hd (superpositionDecode_eq d ⟨k, hw⟩ hne)
  have hl : l' ∈ univ.erase l := mem_erase.2 ⟨hne, mem_univ l'⟩
  by_cases hk : k' = k
  · subst hk
    have := single_le_sum (f := fun l' => if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0)
      (fun l' _ => hind _) hl
    simp only [hw, hk', ↓reduceIte] at this ⊢
    linarith
  have h1 := single_le_sum (f := fun l' => if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0)
    (fun l' _ => hind _) hl
  have h2 := single_le_sum (f := fun k' => ∑ l' ∈ univ.erase l,
      if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0)
    (fun k' _ => sum_nonneg fun l' _ => hind _) (mem_erase.2 ⟨hk, mem_univ k'⟩)
  simp only [hw, hk', ↓reduceIte] at h1 h2 ⊢
  linarith

/-! ### Averaging over the random codebook -/

open Classical in
/-- **Lecture 5, decoder of the satellite message.** Averaged over the random superposition
codebooks, the probability that the satellite message `l` is decoded wrongly, when `(l, k)` is
sent, is at most
`P(E₁₁) + (L - 1) e^{-n(I(X; Y | U) - 4ε)} + (K - 1)(L - 1) e^{-n(I(U, X; Y) - 3ε)}`. -/
theorem sum_codebook_superpositionDecode_le (hq : IsPMF q) (hV : IsChannel V) {n K L : ℕ}
    (ε : ℝ) (d : Fin L) (k : Fin K) (l : Fin L) :
    ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF (superpositionColumnLaw q n L) K C *
        ∑ y, (if superpositionDecode (superpositionTypicalSet q V n ε) C d y ≠ l then
          channelExt V n ((C k).2 l) y else 0) ≤
      superpositionAtypProb q V n ε + (L - 1) * exp (-(n * (superpositionInfoCond q V - 4 * ε))) +
        (K - 1) * (L - 1) *
          exp (-(n * (I[Prod.fst : Prod.snd ; superpositionTriple q V] - 3 * ε))) := by
  set T := superpositionTypicalSet q V n ε
  set ν := superpositionColumnLaw q n L
  have hν := superpositionColumnLaw_isPMF hq n L
  set f₁ : (Fin n → 𝒰) → (Fin n → α) → ℝ :=
    fun u x => ∑ y, channelExt V n x y * (if (u, x, y) ∈ T then 0 else 1)
  set f₂ : (Fin n → 𝒰) → (Fin n → α) → (Fin n → α) → ℝ :=
    fun u x x' => ∑ y, channelExt V n x y * (if (u, x', y) ∈ T then 1 else 0)
  set f₃ : (Fin n → α) → (Fin n → 𝒰) → (Fin n → α) → ℝ :=
    fun x u' x' => ∑ y, channelExt V n x y * (if (u', x', y) ∈ T then 1 else 0)
  set I₁ := superpositionInfoCond q V
  set I₃ := I[Prod.fst : Prod.snd ; superpositionTriple q V]
  -- The error events.
  have hlam : ∀ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
      ∑ y, (if superpositionDecode T C d y ≠ l then channelExt V n ((C k).2 l) y else 0) ≤
        f₁ (C k).1 ((C k).2 l) + ∑ l' ∈ univ.erase l, f₂ (C k).1 ((C k).2 l) ((C k).2 l') +
          ∑ k' ∈ univ.erase k, ∑ l' ∈ univ.erase l, f₃ ((C k).2 l) (C k').1 ((C k').2 l') := by
    intro C
    have h2 : ∑ l' ∈ univ.erase l, f₂ (C k).1 ((C k).2 l) ((C k).2 l') =
        ∑ y, channelExt V n ((C k).2 l) y *
          ∑ l' ∈ univ.erase l, (if ((C k).1, (C k).2 l', y) ∈ T then 1 else 0) := by
      simp only [f₂, mul_sum]
      exact sum_comm
    have h3 : ∑ k' ∈ univ.erase k, ∑ l' ∈ univ.erase l, f₃ ((C k).2 l) (C k').1 ((C k').2 l') =
        ∑ y, channelExt V n ((C k).2 l) y * ∑ k' ∈ univ.erase k, ∑ l' ∈ univ.erase l,
          (if ((C k').1, (C k').2 l', y) ∈ T then 1 else 0) := by
      simp only [f₃, mul_sum]
      calc _ = ∑ k' ∈ univ.erase k, ∑ y, ∑ l' ∈ univ.erase l, channelExt V n ((C k).2 l) y *
            (if ((C k').1, (C k').2 l', y) ∈ T then (1 : ℝ) else 0) :=
            sum_congr rfl fun k' _ => sum_comm
        _ = _ := sum_comm
    rw [h2, h3]
    simp only [f₁, ← sum_add_distrib, ← mul_add]
    refine sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (superpositionDecode_ne_le T C d y k l)
      (channelExt_nonneg hV ((C k).2 l) y)
    rw [mul_ite, mul_one, mul_zero] at this
    exact this
  -- The three averages.
  have hA₁ : ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF ν K C *
      f₁ (C k).1 ((C k).2 l) ≤ superpositionAtypProb q V n ε := by
    have e := sum_iidPMF_eval hν k (fun c => f₁ c.1 (c.2 l))
    beta_reduce at e
    rw [e, sum_superpositionColumnLaw_eval hq l f₁]
    exact sum_superposition_atyp_le hq hV n ε
  have hA₂ : ∀ l' ∈ univ.erase l, ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
      iidPMF ν K C * f₂ (C k).1 ((C k).2 l) ((C k).2 l') ≤ exp (-(n * (I₁ - 4 * ε))) := by
    intro l' hl'
    have e := sum_iidPMF_eval hν k (fun c => f₂ c.1 (c.2 l) (c.2 l'))
    beta_reduce at e
    rw [e, sum_superpositionColumnLaw_eval₂ hq (Ne.symm (ne_of_mem_erase hl')) f₂]
    exact sum_superposition_satellite_le hq hV n ε
  have hA₃ : ∀ k' ∈ univ.erase k, ∀ l' ∈ univ.erase l,
      ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
        iidPMF ν K C * f₃ ((C k).2 l) (C k').1 ((C k').2 l') ≤ exp (-(n * (I₃ - 3 * ε))) := by
    intro k' hk' l' _
    have e := sum_iidPMF_eval₂ hν (Ne.symm (ne_of_mem_erase hk'))
      (fun c c' => f₃ (c.2 l) c'.1 (c'.2 l'))
    beta_reduce at e
    rw [e]
    have e' : ∀ c, ∑ c', superpositionColumnLaw q n L c * superpositionColumnLaw q n L c' *
        f₃ (c.2 l) c'.1 (c'.2 l') = superpositionColumnLaw q n L c *
          ∑ u', ∑ x', jointIid q n (u', x') * f₃ (c.2 l) u' x' := by
      intro c
      rw [← sum_superpositionColumnLaw_eval hq l' (f₃ (c.2 l)), mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    simp only [e']
    rw [sum_superpositionColumnLaw_eval hq l
      (fun _ x => ∑ u', ∑ x', jointIid q n (u', x') * f₃ x u' x')]
    refine le_trans (le_of_eq ?_) (sum_superposition_wrongCloud_le hq hV n ε)
    refine sum_congr rfl fun u _ => sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u' _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun x' _ => by ring
  have hw : ∀ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), 0 ≤ iidPMF ν K C :=
    fun C => iidPMF_nonneg hν.nonneg C
  have hcardL : (#((univ : Finset (Fin L)).erase l) : ℝ) = L - 1 := by
    rw [card_erase_of_mem (mem_univ l), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos l).ne'), Nat.cast_one]
  have hcardK : (#((univ : Finset (Fin K)).erase k) : ℝ) = K - 1 := by
    rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos k).ne'), Nat.cast_one]
  have hpull : ∀ {ι : Type} (s : Finset ι)
      (f : (Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α)) → ι → ℝ),
      ∑ C, iidPMF ν K C * ∑ i ∈ s, f C i = ∑ i ∈ s, ∑ C, iidPMF ν K C * f C i := by
    intro ι s f
    simp only [mul_sum]
    exact sum_comm
  calc _ ≤ ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF ν K C *
        (f₁ (C k).1 ((C k).2 l) + ∑ l' ∈ univ.erase l, f₂ (C k).1 ((C k).2 l) ((C k).2 l') +
          ∑ k' ∈ univ.erase k, ∑ l' ∈ univ.erase l, f₃ ((C k).2 l) (C k').1 ((C k').2 l')) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hlam C) (hw C)
    _ = ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF ν K C *
          f₁ (C k).1 ((C k).2 l) +
        ∑ l' ∈ univ.erase l, ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
          iidPMF ν K C * f₂ (C k).1 ((C k).2 l) ((C k).2 l') +
        ∑ k' ∈ univ.erase k, ∑ l' ∈ univ.erase l,
          ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
            iidPMF ν K C * f₃ ((C k).2 l) (C k').1 ((C k').2 l') := by
        simp only [mul_add, sum_add_distrib]
        rw [hpull, hpull]
        congr 1
        exact sum_congr rfl fun k' _ => hpull _ _
    _ ≤ superpositionAtypProb q V n ε + ∑ _l' ∈ univ.erase l, exp (-(n * (I₁ - 4 * ε))) +
          ∑ _k' ∈ univ.erase k, ∑ _l' ∈ univ.erase l, exp (-(n * (I₃ - 3 * ε))) :=
        add_le_add (add_le_add hA₁ (sum_le_sum hA₂)) (sum_le_sum fun k' hk' =>
          sum_le_sum (hA₃ k' hk'))
    _ = _ := by
        simp only [sum_const, nsmul_eq_mul, hcardL, hcardK]
        ring

open Classical in
/-- **Lecture 5, decoder of the cloud message.** Averaged over the random superposition codebooks,
the probability that the cloud message `k` is decoded wrongly by joint typicality decoding of the
cloud center, when `(l, k)` is sent, is at most `P(E₂₁) + (K - 1) e^{-n(I(U; Y) - 3ε)}`. -/
theorem sum_codebook_superpositionCloudDecode_le (hq : IsPMF q) (hV : IsChannel V) {n K L : ℕ}
    (ε : ℝ) (d : Fin K) (k : Fin K) (l : Fin L) :
    ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α), iidPMF (superpositionColumnLaw q n L) K C *
        ∑ y, (if typicalDecode (jointTypicalSet (superpositionOut q V) n ε) (fun k => (C k).1) d y
          ≠ k then channelExt V n ((C k).2 l) y else 0) ≤
      (1 - prob (jointIid (superpositionOut q V) n) (jointTypicalSet (superpositionOut q V) n ε)) +
        (K - 1) * exp (-(n * (I[Prod.fst : Prod.snd ; superpositionOut q V] - 3 * ε))) := by
  set A := jointTypicalSet (superpositionOut q V) n ε
  have hν := superpositionColumnLaw_isPMF hq n L
  set g₁ : (Fin n → 𝒰) → (Fin n → α) → ℝ :=
    fun u x => ∑ y, channelExt V n x y * (if (u, y) ∈ A then 0 else 1)
  set g₂ : (Fin n → α) → (Fin n → 𝒰) → ℝ :=
    fun x u' => ∑ y, channelExt V n x y * (if (u', y) ∈ A then 1 else 0)
  set I₂ := I[Prod.fst : Prod.snd ; superpositionOut q V]
  have hlam : ∀ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
      ∑ y, (if typicalDecode A (fun k => (C k).1) d y ≠ k then
        channelExt V n ((C k).2 l) y else 0) ≤
        g₁ (C k).1 ((C k).2 l) + ∑ k' ∈ univ.erase k, g₂ ((C k).2 l) (C k').1 := by
    intro C
    have h2 : ∑ k' ∈ univ.erase k, g₂ ((C k).2 l) (C k').1 = ∑ y, channelExt V n ((C k).2 l) y *
        ∑ k' ∈ univ.erase k, (if ((C k').1, y) ∈ A then 1 else 0) := by
      simp only [g₂, mul_sum]
      exact sum_comm
    rw [h2]
    simp only [g₁, ← sum_add_distrib, ← mul_add]
    refine sum_le_sum fun y _ => ?_
    have := mul_le_mul_of_nonneg_left (typicalDecode_ne_le A (fun k => (C k).1) d y k)
      (channelExt_nonneg hV ((C k).2 l) y)
    rw [mul_ite, mul_one, mul_zero] at this
    exact this
  have hA₁ : ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
      iidPMF (superpositionColumnLaw q n L) K C * g₁ (C k).1 ((C k).2 l) =
        1 - prob (jointIid (superpositionOut q V) n) A := by
    rw [sum_iidPMF_eval hν k (fun c => g₁ c.1 (c.2 l)), sum_superpositionColumnLaw_eval hq l g₁]
    exact sum_superposition_cloudAtyp_eq hq hV n ε
  have hA₂ : ∀ k' ∈ univ.erase k, ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
      iidPMF (superpositionColumnLaw q n L) K C * g₂ ((C k).2 l) (C k').1 ≤
        exp (-(n * (I₂ - 3 * ε))) := by
    intro k' hk'
    rw [sum_iidPMF_eval₂ hν (Ne.symm (ne_of_mem_erase hk')) (fun c c' => g₂ (c.2 l) c'.1)]
    have e' : ∀ c, ∑ c', superpositionColumnLaw q n L c * superpositionColumnLaw q n L c' *
        g₂ (c.2 l) c'.1 = superpositionColumnLaw q n L c *
          ∑ u', ∑ x', jointIid q n (u', x') * g₂ (c.2 l) u' := by
      intro c
      rw [← sum_superpositionColumnLaw_eval hq l (fun u' _ => g₂ (c.2 l) u'), mul_sum]
      exact sum_congr rfl fun _ _ => by ring
    simp only [e']
    rw [sum_superpositionColumnLaw_eval hq l
      (fun _ x => ∑ u', ∑ x', jointIid q n (u', x') * g₂ x u')]
    refine le_trans (le_of_eq ?_) (sum_superposition_cloudWrong_le hq hV n ε)
    refine sum_congr rfl fun u _ => sum_congr rfl fun x _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u' _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun x' _ => by ring
  have hcardK : (#((univ : Finset (Fin K)).erase k) : ℝ) = K - 1 := by
    rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Fin.pos k).ne'), Nat.cast_one]
  calc _ ≤ ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
        iidPMF (superpositionColumnLaw q n L) K C *
          (g₁ (C k).1 ((C k).2 l) + ∑ k' ∈ univ.erase k, g₂ ((C k).2 l) (C k').1) :=
        sum_le_sum fun C _ => mul_le_mul_of_nonneg_left (hlam C) (iidPMF_nonneg hν.nonneg C)
    _ = ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
          iidPMF (superpositionColumnLaw q n L) K C * g₁ (C k).1 ((C k).2 l) +
        ∑ k' ∈ univ.erase k, ∑ C : Fin K → (Fin n → 𝒰) × (Fin L → Fin n → α),
          iidPMF (superpositionColumnLaw q n L) K C * g₂ ((C k).2 l) (C k').1 := by
        simp only [mul_add, sum_add_distrib, mul_sum]
        rw [sum_comm (s := univ) (t := univ.erase k)]
    _ ≤ (1 - prob (jointIid (superpositionOut q V) n) A) +
          ∑ _k' ∈ univ.erase k, exp (-(n * (I₂ - 3 * ε))) :=
        add_le_add hA₁.le (sum_le_sum hA₂)
    _ = _ := by
        simp only [sum_const, nsmul_eq_mul, hcardK]

/-! ### The information quantities -/

lemma superposition_sum_mul_snd_eq (f : α → ℝ) :
    ∑ z, q z * f z.2 = ∑ x, margSnd q x * f x := by
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun x _ => ?_
  change ∑ u, q (u, x) * f x = dist q Prod.snd x * f x
  rw [dist_snd, sum_mul]

/-- The law of `(U, Y)` under `p(u, x) V(y | x)`. -/
lemma dist_superpositionTriple_out :
    dist (superpositionTriple q V) (pair (fun z => z.1.1) Prod.snd) = superpositionOut q V := by
  classical
  funext ⟨u, y⟩
  simp [dist, Fintype.sum_prod_type, superpositionTriple, jointOf, superpositionOut, pair, ite_and]

/-- `I(U; Y)` under `p(u, x) V(y | x)` is computed from the law of `(U, Y)`. -/
lemma mutualInfo_superpositionTriple_out :
    I[fun z : (𝒰 × α) × β => z.1.1 : Prod.snd ; superpositionTriple q V] =
      I[Prod.fst : Prod.snd ; superpositionOut q V] := by
  refine mutualInfo_eq_of_dist_pair_eq ?_
  rw [dist_superpositionTriple_out, dist_pair_fst_snd]

/-- `I(X; Y | U) = H(U, X) + H(U, Y) - H(U) - H(U, X, Y)`. -/
lemma condMutualInfo_superpositionTriple (hq : IsPMF q) (hV : IsChannel V) :
    I[fun z : (𝒰 × α) × β => z.1.2 : Prod.snd | fun z => z.1.1 ; superpositionTriple q V] =
      superpositionInfoCond q V := by
  have ht := superpositionTriple_isPMF hq hV
  have hm : dist (superpositionTriple q V) Prod.fst = q := margFst_superpositionTriple hV
  rw [condMutualInfo_eq ht]
  have h1 : H[pair (fun z : (𝒰 × α) × β => z.1.1) (fun z => z.1.2) ;
      superpositionTriple q V] = entropy q := by
    rw [entropyRV, show pair (fun z : (𝒰 × α) × β => z.1.1) (fun z => z.1.2) = Prod.fst from rfl,
      hm]
  have h2 : H[pair (fun z : (𝒰 × α) × β => z.1.1) Prod.snd ; superpositionTriple q V] =
      entropy (superpositionOut q V) := by
    rw [entropyRV, dist_superpositionTriple_out]
  have h3 : H[(fun z : (𝒰 × α) × β => z.1.1) ; superpositionTriple q V] =
      entropy (margFst q) := by
    rw [entropyRV, show (fun z : (𝒰 × α) × β => z.1.1) = Prod.fst ∘ Prod.fst from rfl,
      dist_comp_eq, hm]
  have h4 : H[pair (fun z : (𝒰 × α) × β => z.1.1) (pair (fun z => z.1.2) Prod.snd) ;
      superpositionTriple q V] = entropy (superpositionTriple q V) := by
    have e : H[pair (fun z : (𝒰 × α) × β => z.1.1) (pair (fun z => z.1.2) Prod.snd) ;
        superpositionTriple q V] = H[id ; superpositionTriple q V] :=
      (entropyRV_eq_of_injective _ (fun t : 𝒰 × α × β => ((t.1, t.2.1), t.2.2))
        (fun a b h => by
          obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
          simp only [Prod.mk.injEq] at h ⊢; tauto) (fun _ => rfl)).symm
    rw [e, entropyRV, dist_id]
  rw [h1, h2, h3, h4, superpositionInfoCond]

/-- The Markov chain `U → X → Y`: `I(U, X; Y) = I(X; Y)`. -/
lemma mutualInfo_superpositionTriple_snd (hq : IsPMF q) (hV : IsChannel V) :
    I[fun z : (𝒰 × α) × β => z.1.2 : Prod.snd ; superpositionTriple q V] =
      I[Prod.fst : Prod.snd ; superpositionTriple q V] := by
  classical
  set pX := margSnd q
  have hpX : IsPMF pX := hq.dist _
  have hd : dist (superpositionTriple q V) (pair (fun z => z.1.2) Prod.snd) = jointOf pX V := by
    funext ⟨x, y⟩
    have h : dist q Prod.snd x = ∑ u, q (u, x) := dist_snd q x
    simp only [pX, jointOf, h]
    simp [dist, Fintype.sum_prod_type, superpositionTriple, jointOf, pair, ite_and, sum_mul]
  have ht := superpositionTriple_isPMF hq hV
  have hj := jointOf_isPMF hpX hV
  have e1 : I[fun z : (𝒰 × α) × β => z.1.2 : Prod.snd ; superpositionTriple q V] =
      I[Prod.fst : Prod.snd ; jointOf pX V] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [hd, dist_pair_fst_snd]
  have hc1 := condEntropy_snd_fst_eq hj
  rw [condEntropy_jointOf hpX hV, margFst, dist_jointOf_fst hV] at hc1
  have hm : dist (superpositionTriple q V) Prod.fst = q := margFst_superpositionTriple hV
  have hc2 : ∑ x, pX x * entropy (V x) = entropy (superpositionTriple q V) - entropy q := by
    have h := condEntropy_snd_fst_eq ht
    rw [margFst, hm, superpositionTriple, condEntropy_jointOf hq (fun z => hV z.2),
      superposition_sum_mul_snd_eq (q := q) fun x => entropy (V x)] at h
    exact h
  have hs : margSnd (superpositionTriple q V) = margSnd (jointOf pX V) := by
    change dist (jointOf q fun z => V z.2) Prod.snd = dist (jointOf pX V) Prod.snd
    rw [dist_jointOf_snd, dist_jointOf_snd]
    funext y
    exact superposition_sum_mul_snd_eq (q := q) fun x => V x y
  have hmj : margFst (jointOf pX V) = pX := dist_jointOf_fst hV
  have hm' : margFst (superpositionTriple q V) = q := hm
  rw [e1, mutualInfo_fst_snd_eq hj, mutualInfo_fst_snd_eq ht, hm', hs, hmj]
  linarith

section Marginals

variable {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

lemma superposition_dist_bcJoint_fst :
    dist (bcJoint q W) (fun z => (z.1, z.2.1)) = superpositionTriple q (bcMarg₁ W) := by
  classical
  funext ⟨⟨u, x⟩, y⟩
  simp [dist, Fintype.sum_prod_type, superpositionTriple, bcJoint, jointOf, bcMarg₁, ite_and,
    mul_sum]

lemma superposition_dist_bcJoint_snd :
    dist (bcJoint q W) (fun z => (z.1, z.2.2)) = superpositionTriple q (bcMarg₂ W) := by
  classical
  funext ⟨⟨u, x⟩, y⟩
  simp [dist, Fintype.sum_prod_type, superpositionTriple, bcJoint, jointOf, bcMarg₂, ite_and,
    mul_sum]

/-- Conditional mutual information of functions of `G` only depends on the law of `G`. -/
lemma condMutualInfo_comp_superposition {Ω T γ δ ε' : Type*} [Fintype Ω] [Fintype T] [Fintype γ]
    [Fintype δ] [Fintype ε'] {μ : Ω → ℝ} (hμ : IsPMF μ) (G : Ω → T) (X : T → γ) (Y : T → δ)
    (Z : T → ε') : I[X ∘ G : Y ∘ G | Z ∘ G ; μ] = I[X : Y | Z ; dist μ G] := by
  rw [condMutualInfo_eq hμ, condMutualInfo_eq (hμ.dist G)]
  simp only [entropyRV]
  rw [show pair (Z ∘ G) (X ∘ G) = pair Z X ∘ G from rfl,
    show pair (Z ∘ G) (Y ∘ G) = pair Z Y ∘ G from rfl,
    show pair (Z ∘ G) (pair (X ∘ G) (Y ∘ G)) = pair Z (pair X Y) ∘ G from rfl]
  simp only [dist_comp_eq]

lemma superposition_bcInfoXY₁U_eq (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₁U q W = superpositionInfoCond q (bcMarg₁ W) := by
  have h := condMutualInfo_comp_superposition (bcJoint_isPMF hq hW)
    (fun z : (𝒰 × α) × (β₁ × β₂) => (z.1, z.2.1)) (fun z => z.1.2) Prod.snd (fun z => z.1.1)
  rw [superposition_dist_bcJoint_fst, condMutualInfo_superpositionTriple hq hW.bcMarg₁] at h
  exact h

lemma superposition_bcInfoXY₂U_eq (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₂U q W = superpositionInfoCond q (bcMarg₂ W) := by
  have h := condMutualInfo_comp_superposition (bcJoint_isPMF hq hW)
    (fun z : (𝒰 × α) × (β₁ × β₂) => (z.1, z.2.2)) (fun z => z.1.2) Prod.snd (fun z => z.1.1)
  rw [superposition_dist_bcJoint_snd, condMutualInfo_superpositionTriple hq hW.bcMarg₂] at h
  exact h

lemma superposition_bcInfoUY₁_eq :
    bcInfoUY₁ q W = I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₁ W)] := by
  have h : bcInfoUY₁ q W = I[fun z : (𝒰 × α) × β₁ => z.1.1 : Prod.snd ;
      dist (bcJoint q W) (fun z => (z.1, z.2.1))] :=
    mutualInfo_eq_of_dist_pair_eq (dist_comp_eq (bcJoint q W) (fun z => (z.1, z.2.1))
      (pair (fun z => z.1.1) Prod.snd))
  rw [h, superposition_dist_bcJoint_fst, mutualInfo_superpositionTriple_out]

lemma superposition_bcInfoUY₂_eq :
    bcInfoUY₂ q W = I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₂ W)] := by
  have h : bcInfoUY₂ q W = I[fun z : (𝒰 × α) × β₂ => z.1.1 : Prod.snd ;
      dist (bcJoint q W) (fun z => (z.1, z.2.2))] :=
    mutualInfo_eq_of_dist_pair_eq (dist_comp_eq (bcJoint q W) (fun z => (z.1, z.2.2))
      (pair (fun z => z.1.1) Prod.snd))
  rw [h, superposition_dist_bcJoint_snd, mutualInfo_superpositionTriple_out]

lemma superposition_bcInfoXY₁_eq (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₁ q W = I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₁ W)] := by
  have h : bcInfoXY₁ q W = I[fun z : (𝒰 × α) × β₁ => z.1.2 : Prod.snd ;
      dist (bcJoint q W) (fun z => (z.1, z.2.1))] :=
    mutualInfo_eq_of_dist_pair_eq (dist_comp_eq (bcJoint q W) (fun z => (z.1, z.2.1))
      (pair (fun z => z.1.2) Prod.snd))
  rw [h, superposition_dist_bcJoint_fst, mutualInfo_superpositionTriple_snd hq hW.bcMarg₁]

lemma superposition_bcInfoXY₂_eq (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₂ q W = I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₂ W)] := by
  have h : bcInfoXY₂ q W = I[fun z : (𝒰 × α) × β₂ => z.1.2 : Prod.snd ;
      dist (bcJoint q W) (fun z => (z.1, z.2.2))] :=
    mutualInfo_eq_of_dist_pair_eq (dist_comp_eq (bcJoint q W) (fun z => (z.1, z.2.2))
      (pair (fun z => z.1.2) Prod.snd))
  rw [h, superposition_dist_bcJoint_snd, mutualInfo_superpositionTriple_snd hq hW.bcMarg₂]

end Marginals

/-! ### Existence of a good code -/

section Code

variable {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

omit [Fintype α] in
open Classical in
/-- If the probabilities of error for each message pair at both receivers, averaged over a random
code, are at most `b₁` and `b₂`, then some code has probability of error at most `b₁ + b₂`. -/
lemma exists_bcCode_errProb_le_of_sum_codebook {Θ : Type*} [Fintype Θ] {P : Θ → ℝ}
    (hP : IsPMF P) (hW : IsChannel W) {M₁ M₂ n : ℕ} (h₁ : 0 < M₁) (h₂ : 0 < M₂)
    (code : Θ → BCCode M₁ M₂ n α β₁ β₂) {b₁ b₂ : ℝ}
    (hb₁ : ∀ w : Fin M₁ × Fin M₂, ∑ θ, P θ * ∑ y,
      (if (code θ).dec₁ y ≠ w.1 then channelExt (bcMarg₁ W) n ((code θ).enc w) y else 0) ≤ b₁)
    (hb₂ : ∀ w : Fin M₁ × Fin M₂, ∑ θ, P θ * ∑ y,
      (if (code θ).dec₂ y ≠ w.2 then channelExt (bcMarg₂ W) n ((code θ).enc w) y else 0) ≤ b₂) :
    ∃ θ, (code θ).errProb W ≤ b₁ + b₂ := by
  have hM : (0 : ℝ) < M₁ * M₂ := by positivity
  have key : ∀ (e : Θ → Fin M₁ × Fin M₂ → ℝ) {b : ℝ}, (∀ w, ∑ θ, P θ * e θ w ≤ b) →
      ∑ θ, P θ * ((∑ w, e θ w) / (M₁ * M₂)) ≤ b := by
    intro e b he
    have e1 : ∑ θ, P θ * ((∑ w, e θ w) / (M₁ * M₂)) = (∑ w, ∑ θ, P θ * e θ w) / (M₁ * M₂) := by
      simp only [mul_div_assoc', ← sum_div, mul_sum]
      congr 1
      exact sum_comm
    rw [e1, div_le_iff₀ hM]
    calc _ ≤ ∑ _w : Fin M₁ × Fin M₂, b := sum_le_sum fun w _ => he w
      _ = b * (M₁ * M₂) := by simp [sum_const, card_univ, mul_comm]
  have h : ∑ θ, P θ * ((code θ).errProb₁ W + (code θ).errProb₂ W) ≤ b₁ + b₂ := by
    simp only [mul_add, sum_add_distrib]
    exact add_le_add (key _ hb₁) (key _ hb₂)
  obtain ⟨θ, hθ⟩ := exists_le_of_sum_mul_le hP h
  exact ⟨θ, ((code θ).errProb_le_add hW).trans hθ⟩

/-- **Lecture 5.** Superposition coding with receiver 1 decoding the satellite codewords and
receiver 2 the cloud centers. -/
theorem exists_bcCode_superposition (hq : IsPMF q) (hW : IsChannel W) {M₁ M₂ n : ℕ} (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) (ε : ℝ) :
    ∃ c : BCCode M₁ M₂ n α β₁ β₂, c.errProb W ≤
      (superpositionAtypProb q (bcMarg₁ W) n ε +
          (M₁ - 1) * exp (-(n * (superpositionInfoCond q (bcMarg₁ W) - 4 * ε))) +
          (M₂ - 1) * (M₁ - 1) *
            exp (-(n * (I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₁ W)] - 3 * ε)))) +
        ((1 - prob (jointIid (superpositionOut q (bcMarg₂ W)) n)
            (jointTypicalSet (superpositionOut q (bcMarg₂ W)) n ε)) +
          (M₂ - 1) *
            exp (-(n * (I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₂ W)] - 3 * ε)))) := by
  classical
  have hP := iidPMF_isPMF (superpositionColumnLaw_isPMF hq n M₁) M₂
  let code : (Fin M₂ → (Fin n → 𝒰) × (Fin M₁ → Fin n → α)) → BCCode M₁ M₂ n α β₁ β₂ := fun C =>
    ⟨fun w => (C w.2).2 w.1,
      superpositionDecode (superpositionTypicalSet q (bcMarg₁ W) n ε) C ⟨0, h₁⟩,
      typicalDecode (jointTypicalSet (superpositionOut q (bcMarg₂ W)) n ε) (fun k => (C k).1)
        ⟨0, h₂⟩⟩
  obtain ⟨C, hC⟩ := exists_bcCode_errProb_le_of_sum_codebook hP hW h₁ h₂ code
    (fun w => sum_codebook_superpositionDecode_le hq hW.bcMarg₁ ε _ w.2 w.1)
    (fun w => sum_codebook_superpositionCloudDecode_le hq hW.bcMarg₂ ε _ w.2 w.1)
  exact ⟨code C, hC⟩

/-- **Lecture 5.** Superposition coding with receiver 1 decoding the cloud centers and receiver 2
the satellite codewords. -/
theorem exists_bcCode_superposition₂ (hq : IsPMF q) (hW : IsChannel W) {M₁ M₂ n : ℕ} (h₁ : 0 < M₁)
    (h₂ : 0 < M₂) (ε : ℝ) :
    ∃ c : BCCode M₁ M₂ n α β₁ β₂, c.errProb W ≤
      ((1 - prob (jointIid (superpositionOut q (bcMarg₁ W)) n)
            (jointTypicalSet (superpositionOut q (bcMarg₁ W)) n ε)) +
          (M₁ - 1) *
            exp (-(n * (I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₁ W)] - 3 * ε)))) +
        (superpositionAtypProb q (bcMarg₂ W) n ε +
          (M₂ - 1) * exp (-(n * (superpositionInfoCond q (bcMarg₂ W) - 4 * ε))) +
          (M₁ - 1) * (M₂ - 1) *
            exp (-(n * (I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₂ W)] - 3 * ε)))) := by
  classical
  have hP := iidPMF_isPMF (superpositionColumnLaw_isPMF hq n M₂) M₁
  let code : (Fin M₁ → (Fin n → 𝒰) × (Fin M₂ → Fin n → α)) → BCCode M₁ M₂ n α β₁ β₂ := fun C =>
    ⟨fun w => (C w.1).2 w.2,
      typicalDecode (jointTypicalSet (superpositionOut q (bcMarg₁ W)) n ε) (fun k => (C k).1)
        ⟨0, h₁⟩,
      superpositionDecode (superpositionTypicalSet q (bcMarg₂ W) n ε) C ⟨0, h₂⟩⟩
  obtain ⟨C, hC⟩ := exists_bcCode_errProb_le_of_sum_codebook hP hW h₁ h₂ code
    (fun w => sum_codebook_superpositionCloudDecode_le hq hW.bcMarg₁ ε _ w.1 w.2)
    (fun w => sum_codebook_superpositionDecode_le hq hW.bcMarg₂ ε _ w.1 w.2)
  exact ⟨code C, hC⟩

end Code

/-! ### The rates -/

lemma superposition_two_pow_ceil_sub_one_le (n : ℕ) (R : ℝ) :
    ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) - 1 ≤ 2 * exp (n * (R * log 2)) := by
  rcases le_or_gt R 0 with h | h
  · rw [Nat.ceil_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) h)]
    simp only [pow_zero, Nat.cast_one, sub_self]
    positivity
  · linarith [two_pow_ceil_le n h.le]

lemma superposition_two_pow_sub_one_nonneg (k : ℕ) : 0 ≤ ((2 ^ k : ℕ) : ℝ) - 1 := by
  have : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
  linarith

lemma superposition_mul_exp_le {a c r I t ε : ℝ} {n : ℕ} (ha : a ≤ c * exp (n * r)) (hc : 0 ≤ c)
    (h : r + t * ε + ε ≤ I) : a * exp (-(n * (I - t * ε))) ≤ c * exp (-(n * ε)) := by
  calc a * exp (-(n * (I - t * ε))) ≤ c * exp (n * r) * exp (-(n * (I - t * ε))) :=
        mul_le_mul_of_nonneg_right ha (exp_pos _).le
    _ = c * exp (n * r + -(n * (I - t * ε))) := by rw [mul_assoc, exp_add]
    _ ≤ c * exp (-(n * ε)) := mul_le_mul_of_nonneg_left
        (exp_le_exp.2 (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])) hc

/-- With `L = 2^⌈nR_s⌉` satellite messages and `K = 2^⌈nR_c⌉` cloud messages, the terms of the
random coding bound decay exponentially, by the conditions on the rates. -/
lemma superposition_rate_terms_le {n : ℕ} {Rs Rc I₁ I₂ I₃ ε : ℝ} (hε : 0 < ε)
    (h₁ : Rs * log 2 + 5 * ε ≤ I₁) (h₂ : Rc * log 2 + 5 * ε ≤ I₂)
    (h₃ : (Rs + Rc) * log 2 + 5 * ε ≤ I₃) :
    (((2 ^ ⌈n * Rs⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (I₁ - 4 * ε))) +
        (((2 ^ ⌈n * Rc⌉₊ : ℕ) : ℝ) - 1) * (((2 ^ ⌈n * Rs⌉₊ : ℕ) : ℝ) - 1) *
          exp (-(n * (I₃ - 3 * ε))) +
        (((2 ^ ⌈n * Rc⌉₊ : ℕ) : ℝ) - 1) * exp (-(n * (I₂ - 3 * ε))) ≤
      8 * exp (-(n * ε)) := by
  have hs := superposition_two_pow_ceil_sub_one_le n Rs
  have hc := superposition_two_pow_ceil_sub_one_le n Rc
  have e1 := superposition_mul_exp_le (t := 4) (I := I₁) (ε := ε) hs (by norm_num) (by linarith)
  have e3 := superposition_mul_exp_le (t := 3) (I := I₂) (ε := ε) hc (by norm_num) (by linarith)
  have hcs : (((2 ^ ⌈n * Rc⌉₊ : ℕ) : ℝ) - 1) * (((2 ^ ⌈n * Rs⌉₊ : ℕ) : ℝ) - 1) ≤
      4 * exp (n * ((Rs + Rc) * log 2)) := by
    calc _ ≤ (2 * exp (n * (Rc * log 2))) * (2 * exp (n * (Rs * log 2))) :=
          mul_le_mul hc hs (superposition_two_pow_sub_one_nonneg _) (by positivity)
      _ = _ := by
          rw [show (n : ℝ) * ((Rs + Rc) * log 2) = n * (Rc * log 2) + n * (Rs * log 2) by ring,
            exp_add]
          ring
  have e2 := superposition_mul_exp_le (t := 3) (I := I₃) (ε := ε) hcs (by norm_num) (by linarith)
  linarith

/-- A common slack `ε` for three strict inequalities. -/
lemma superposition_exists_slack {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ 5 * ε ≤ a ∧ 5 * ε ≤ b ∧ 5 * ε ≤ c := by
  refine ⟨min (min a b) c / 5, by positivity, ?_, ?_, ?_⟩
  · linarith [(min_le_left (min a b) c).trans (min_le_left a b)]
  · linarith [(min_le_left (min a b) c).trans (min_le_right a b)]
  · linarith [min_le_right (min a b) c]

/-- The bound on the probability of error tends to `0`. -/
lemma tendsto_superposition_errBound {β' β'' : Type*} [Fintype β'] [Fintype β'']
    {Vs : α → β' → ℝ} {Vc : α → β'' → ℝ} (hq : IsPMF q) (hVs : IsChannel Vs) (hVc : IsChannel Vc)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => superpositionAtypProb q Vs n ε +
      (1 - prob (jointIid (superpositionOut q Vc) n)
        (jointTypicalSet (superpositionOut q Vc) n ε)) + 8 * exp (-(n * ε))) atTop (𝓝 0) := by
  have h₁ := tendsto_superpositionAtypProb hq hVs hε
  have h₂ := (tendsto_prob_jointTypicalSet (superpositionOut_isPMF hq hVc) hε).const_sub 1
  have h₃ := (tendsto_exp_neg_mul_nat hε).const_mul 8
  simpa using (h₁.add h₂).add h₃

/-! ### The superposition coding inner bound -/

variable {β₁ β₂ : Type*} [Fintype β₁] [Fintype β₂] {W : α → β₁ × β₂ → ℝ}

omit [Fintype α] in
/-- The probability of error of a broadcast code is nonnegative. -/
lemma superposition_errProb_nonneg (hW : IsChannel W) {M₁ M₂ n : ℕ}
    (c : BCCode M₁ M₂ n α β₁ β₂) : 0 ≤ c.errProb W :=
  (c.errProb₁_nonneg hW).trans ((le_max_left _ _).trans (c.max_errProb_le hW))

/-- **Theorem 1 of [elgamal2010], Lecture 5 (Superposition coding inner bound).** A rate pair
`(R₁, R₂)`, in bits, is achievable for the DM-BC if `R₁ < I(X; Y₁ | U)`, `R₂ < I(U; Y₂)` and
`R₁ + R₂ < I(X; Y₁)` for some `p(u, x)`. -/
theorem superpositionRegionBits_subset (hW : IsChannel W) :
    superpositionRegionBits W ⊆ {R | IsAchievableBCBits W R.1 R.2} := by
  rintro ⟨R₁, R₂⟩ ⟨k, q, hq, h₁, h₂, h₃⟩
  dsimp only at h₁ h₂ h₃ ⊢
  have hl := log_pos one_lt_two
  rw [superposition_bcInfoXY₁U_eq hq hW, lt_div_iff₀ hl] at h₁
  rw [superposition_bcInfoUY₂_eq, lt_div_iff₀ hl] at h₂
  rw [superposition_bcInfoXY₁_eq hq hW, lt_div_iff₀ hl] at h₃
  obtain ⟨ε, hε, e₁, e₂, e₃⟩ := superposition_exists_slack (sub_pos.2 h₁) (sub_pos.2 h₂)
    (sub_pos.2 h₃)
  have hP := tendsto_superposition_errBound hq hW.bcMarg₁ hW.bcMarg₂ hε
  have hcode : ∀ n : ℕ, ∃ c : BCCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α β₁ β₂,
      c.errProb W ≤ superpositionAtypProb q (bcMarg₁ W) n ε +
        (1 - prob (jointIid (superpositionOut q (bcMarg₂ W)) n)
          (jointTypicalSet (superpositionOut q (bcMarg₂ W)) n ε)) + 8 * exp (-(n * ε)) := by
    intro n
    obtain ⟨c, hc⟩ := exists_bcCode_superposition (n := n) hq hW
      (M₁ := 2 ^ ⌈n * R₁⌉₊) (M₂ := 2 ^ ⌈n * R₂⌉₊) (by positivity) (by positivity) ε
    refine ⟨c, hc.trans ?_⟩
    have := superposition_rate_terms_le (n := n) (Rs := R₁) (Rc := R₂)
      (I₁ := superpositionInfoCond q (bcMarg₁ W))
      (I₂ := I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₂ W)])
      (I₃ := I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₁ W)]) hε (by linarith)
      (by linarith) (by linarith)
    linarith
  choose c hc using hcode
  exact ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP
    (fun n => superposition_errProb_nonneg hW (c n)) hc⟩

/-- **Lecture 5 of [elgamal2010], remark after Theorem 1.** The superposition coding inner bound
with the roles of the receivers exchanged: `(R₁, R₂)`, in bits, is achievable if `R₁ < I(U; Y₁)`,
`R₂ < I(X; Y₂ | U)` and `R₁ + R₂ < I(X; Y₂)` for some `p(u, x)`. -/
theorem superpositionRegionBits₂_subset (hW : IsChannel W) :
    superpositionRegionBits₂ W ⊆ {R | IsAchievableBCBits W R.1 R.2} := by
  rintro ⟨R₁, R₂⟩ ⟨k, q, hq, h₁, h₂, h₃⟩
  dsimp only at h₁ h₂ h₃ ⊢
  have hl := log_pos one_lt_two
  rw [superposition_bcInfoUY₁_eq, lt_div_iff₀ hl] at h₁
  rw [superposition_bcInfoXY₂U_eq hq hW, lt_div_iff₀ hl] at h₂
  rw [superposition_bcInfoXY₂_eq hq hW, lt_div_iff₀ hl] at h₃
  obtain ⟨ε, hε, e₁, e₂, e₃⟩ := superposition_exists_slack (sub_pos.2 h₁) (sub_pos.2 h₂)
    (sub_pos.2 h₃)
  have hP := tendsto_superposition_errBound hq hW.bcMarg₂ hW.bcMarg₁ hε
  have hcode : ∀ n : ℕ, ∃ c : BCCode (2 ^ ⌈n * R₁⌉₊) (2 ^ ⌈n * R₂⌉₊) n α β₁ β₂,
      c.errProb W ≤ superpositionAtypProb q (bcMarg₂ W) n ε +
        (1 - prob (jointIid (superpositionOut q (bcMarg₁ W)) n)
          (jointTypicalSet (superpositionOut q (bcMarg₁ W)) n ε)) + 8 * exp (-(n * ε)) := by
    intro n
    obtain ⟨c, hc⟩ := exists_bcCode_superposition₂ (n := n) hq hW
      (M₁ := 2 ^ ⌈n * R₁⌉₊) (M₂ := 2 ^ ⌈n * R₂⌉₊) (by positivity) (by positivity) ε
    refine ⟨c, hc.trans ?_⟩
    have := superposition_rate_terms_le (n := n) (Rs := R₂) (Rc := R₁)
      (I₁ := superpositionInfoCond q (bcMarg₂ W))
      (I₂ := I[Prod.fst : Prod.snd ; superpositionOut q (bcMarg₁ W)])
      (I₃ := I[Prod.fst : Prod.snd ; superpositionTriple q (bcMarg₂ W)]) hε (by linarith)
      (by linarith) (by linarith)
    linarith
  choose c hc using hcode
  exact ⟨c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hP
    (fun n => superposition_errProb_nonneg hW (c n)) hc⟩

end InfoTheory
