/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.MutualInformation.ChainRule
public import InfoTheoryLib.Network.SourceHelper
public import InfoTheoryLib.StateChannel.GPDerandomize

/-!
# Lossless source coding with a helper: the converse

This file proves the converse of Theorem 2 of Lecture 11, with `Uᵢ = (M₂, Xⁱ⁻¹, Yⁱ⁻¹)`.

We bound the helper differently from the notes, which use a Markov chain for
`I(Yᵢ; M₂ | Yⁱ⁻¹) = I(Yᵢ; M₂, Yⁱ⁻¹, Xⁱ⁻¹)`. With `Zᵢ = (Xᵢ, Yᵢ)`, the independence of `Yᵢ` and
`Zⁱ⁻¹` gives `I(Yᵢ; Uᵢ) = I(Yᵢ; M₂ | Zⁱ⁻¹) ≤ I(Zᵢ; M₂ | Zⁱ⁻¹)`, and the chain rule bounds the sum of
the last terms by `H(M₂)`.

## Main statements

* `sum_iidPMF_mul_phi`: summing over one coordinate of an i.i.d. sequence.
* `entropyRV_mix`, `condEntropy_mix`: the entropies under a uniform time sharing variable.
* `HelperCode.exists_kernel_le`: the single-letter bounds for one code.
* `IsAchievableHelperBits.mem_closure_helperRegionBits`: **the converse of Theorem 2 of Lecture
  11**.
* `helperOptimalRegionBits_eq`: **Theorem 2 of Lecture 11**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 11
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### One coordinate of an i.i.d. sequence -/

section IID

variable {γ : Type*} [Fintype γ] {n : ℕ}

open Classical in
/-- The product over the other coordinates. -/
private def otherProd (q : γ → ℝ) (i : Fin n) (ω : Fin n → γ) : ℝ := ∏ j ∈ univ.erase i, q (ω j)

omit [Fintype γ] in
open Classical in
private lemma iidPMF_eq_mul_otherProd (q : γ → ℝ) (i : Fin n) (ω : Fin n → γ) :
    iidPMF q n ω = q (ω i) * otherProd q i ω :=
  (mul_prod_erase univ (fun j => q (ω j)) (mem_univ i)).symm

omit [Fintype γ] in
open Classical in
private lemma otherProd_update (q : γ → ℝ) (i : Fin n) (ω : Fin n → γ) (c : γ) :
    otherProd q i (Function.update ω i c) = otherProd q i ω :=
  prod_congr rfl fun j hj => by rw [Function.update_of_ne (mem_erase.1 hj).1]

open Classical in
/-- **Summing over one coordinate.** If `G` does not depend on the coordinate `i` on the support of
`φ`, the sum `∑_ω p(ω) φ(ωᵢ) G(ω)` factors as `(∑_c q(c) φ(c)) T`, with `T` not depending on `φ`. -/
theorem sum_iidPMF_mul_phi (q : γ → ℝ) (i : Fin n) (c₀ : γ) (G : (Fin n → γ) → ℝ) :
    ∃ T : ℝ, ∀ φ : γ → ℝ,
      (∀ ω c, φ c ≠ 0 → G (Function.update ω i c) = G (Function.update ω i c₀)) →
      ∑ ω, iidPMF q n ω * (φ (ω i) * G ω) = (∑ c, q c * φ c) * T := by
  refine ⟨∑ g : {j // j ≠ i} → γ, otherProd q i ((Equiv.funSplitAt i γ).symm (c₀, g)) *
    G ((Equiv.funSplitAt i γ).symm (c₀, g)), fun φ hG => ?_⟩
  have hsym : ∀ (c : γ) (g : {j // j ≠ i} → γ), (Equiv.funSplitAt i γ).symm (c, g) =
      Function.update ((Equiv.funSplitAt i γ).symm (c₀, g)) i c := fun c g => by
    funext j
    by_cases h : j = i
    · subst h
      simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, h]
  have hval : ∀ (c : γ) (g : {j // j ≠ i} → γ), (Equiv.funSplitAt i γ).symm (c, g) i = c :=
    fun c g => by simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [← (Equiv.funSplitAt i γ).symm.sum_comp, Fintype.sum_prod_type]
  simp only [iidPMF_eq_mul_otherProd q i, hval]
  rw [sum_mul]
  refine sum_congr rfl fun c _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun g _ => ?_
  by_cases hφ : φ c = 0
  · simp [hφ]
  · have h1 : G ((Equiv.funSplitAt i γ).symm (c, g)) = G ((Equiv.funSplitAt i γ).symm (c₀, g)) := by
      rw [hsym c g, hG _ c hφ]
      congr 1
      rw [← hsym c₀ g]
    have h2 : otherProd q i ((Equiv.funSplitAt i γ).symm (c, g)) =
        otherProd q i ((Equiv.funSplitAt i γ).symm (c₀, g)) := by
      rw [hsym c g, otherProd_update]
    rw [h1, h2]
    ring

end IID

/-! ### Uniform time sharing -/

section Mix

variable {Ω ι a : Type*} [Fintype Ω] [Fintype ι] [Fintype a] {b : ι → Type*}
  [∀ i, Fintype (b i)] {μ : Ω → ℝ}

/-- The law of `(ω, Q)` with `Q` uniform and independent of `ω`. -/
def mixLaw (μ : Ω → ℝ) (ι : Type*) [Fintype ι] : Ω × ι → ℝ := prodDist μ (uniformPMF ι)

lemma mixLaw_isPMF [Nonempty ι] (hμ : IsPMF μ) : IsPMF (mixLaw μ ι) :=
  hμ.prodDist uniformPMF_isPMF

omit [∀ i, Fintype (b i)] in
open Classical in
lemma dist_mix_sigma (f : ∀ i, Ω → b i) (i : ι) (v : b i) :
    dist (mixLaw μ ι) (fun z => (⟨z.2, f z.2 z.1⟩ : Σ i, b i)) ⟨i, v⟩ =
      (Fintype.card ι : ℝ)⁻¹ * dist μ (f i) v := by
  simp only [dist, mixLaw, prodDist, uniformPMF, Fintype.sum_prod_type_right]
  rw [sum_eq_single i]
  · rw [mul_sum]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h : f i ω = v
    · simp [h]
      ring
    · simp [h]
  · intro j _ hj
    refine sum_eq_zero fun ω _ => ?_
    simp [hj]
  · simp

/-- **Lecture 11, page 11-31.** The entropy of `(Q, f_Q)` under uniform time sharing. -/
theorem entropyRV_mix [Nonempty ι] (hμ : IsPMF μ) (f : ∀ i, Ω → b i) :
    H[fun z : Ω × ι => (⟨z.2, f z.2 z.1⟩ : Σ i, b i) ; mixLaw μ ι] =
      log (Fintype.card ι) + (Fintype.card ι : ℝ)⁻¹ * ∑ i, H[f i ; μ] := by
  classical
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [entropyRV, entropy_eq_sum_negMulLog, Fintype.sum_sigma, mul_sum]
  simp only [dist_mix_sigma]
  have hterm : ∀ i, ∑ v, negMulLog ((Fintype.card ι : ℝ)⁻¹ * dist μ (f i) v) =
      (Fintype.card ι : ℝ)⁻¹ * log (Fintype.card ι) + (Fintype.card ι : ℝ)⁻¹ * H[f i ; μ] := by
    intro i
    have h1 : ∀ v, negMulLog ((Fintype.card ι : ℝ)⁻¹ * dist μ (f i) v) =
        dist μ (f i) v * ((Fintype.card ι : ℝ)⁻¹ * log (Fintype.card ι)) +
          (Fintype.card ι : ℝ)⁻¹ * negMulLog (dist μ (f i) v) := fun v => by
      rcases eq_or_ne (dist μ (f i) v) 0 with h | h
      · simp [h]
      · rw [negMulLog, negMulLog, log_mul (inv_ne_zero hN.ne') h, log_inv]
        ring
    simp only [h1]
    rw [sum_add_distrib, ← sum_mul, (hμ.dist _).sum_eq_one, one_mul, ← mul_sum, entropyRV,
      entropy_eq_sum_negMulLog]
  simp only [hterm]
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hN.ne',
    one_mul]

/-- **Lecture 11, page 11-31.** `H(A_Q | Q, U_Q) = (1/n) ∑ᵢ H(Aᵢ | Uᵢ)` under uniform time sharing.
-/
theorem condEntropy_mix [Nonempty ι] (hμ : IsPMF μ) (A : ι → Ω → a) (U : ∀ i, Ω → b i) :
    H[fun z : Ω × ι => A z.2 z.1 | fun z => (⟨z.2, U z.2 z.1⟩ : Σ i, b i) ; mixLaw μ ι] =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, H[A i | U i ; μ] := by
  classical
  have hν : IsPMF (mixLaw μ ι) := mixLaw_isPMF hμ
  rw [condEntropy_eq_sub hν, entropyRV_mix hμ U]
  have e : H[pair (fun z : Ω × ι => (⟨z.2, U z.2 z.1⟩ : Σ i, b i)) fun z => A z.2 z.1 ;
      mixLaw μ ι] =
      H[fun z : Ω × ι => (⟨z.2, pair (U z.2) (A z.2) z.1⟩ : Σ i, b i × a) ; mixLaw μ ι] := by
    refine entropyRV_eq_of_injective _ (fun s : Σ i, b i × a => ((⟨s.1, s.2.1⟩ : Σ i, b i), s.2.2))
      ?_ fun _ => rfl
    rintro ⟨i, u, x⟩ ⟨i', u', x'⟩ h
    simp only [Prod.mk.injEq, Sigma.mk.injEq] at h
    obtain ⟨⟨rfl, hu⟩, rfl⟩ := h
    simp only [heq_eq_eq] at hu
    rw [hu]
  rw [e, entropyRV_mix hμ fun i => pair (U i) (A i)]
  have h3 : ∑ i, H[pair (U i) (A i) ; μ] = ∑ i, H[U i ; μ] + ∑ i, H[A i | U i ; μ] := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => chain_rule hμ _ _
  rw [h3]
  ring

end Mix

/-! ### The bounds for one code -/

section Converse

variable {α β : Type*} [Fintype α] [Fintype β] {q : α × β → ℝ} {n M₁ M₂ : ℕ}

/-- The pair at the time `k`, for `k < n`. -/
def seqZ (z₀ : α × β) (k : ℕ) (ω : Fin n → α × β) : α × β :=
  if h : k < n then ω ⟨k, h⟩ else z₀

omit [Fintype α] [Fintype β] in
lemma seqZ_coe (z₀ : α × β) (i : Fin n) (ω : Fin n → α × β) : seqZ z₀ i ω = ω i := by
  simp [seqZ]

open Classical in
omit [Fintype α] [Fintype β] in
/-- The past `Zⁱ⁻¹` does not depend on the coordinate `i`. -/
lemma prefixRV_update (z₀ : α × β) (i : Fin n) (ω : Fin n → α × β) (c : α × β) :
    prefixRV (seqZ z₀) i (Function.update ω i c) = prefixRV (seqZ z₀) i ω := by
  funext j
  have hj : (j : ℕ) < n := j.isLt.trans i.isLt
  have hne : (⟨j, hj⟩ : Fin n) ≠ i := fun h => absurd (congrArg Fin.val h) (ne_of_lt j.isLt)
  have e : ∀ ω₁ : Fin n → α × β, seqZ z₀ j ω₁ = ω₁ ⟨j, hj⟩ := fun ω₁ => by simp [seqZ, hj]
  simp only [prefixRV]
  rw [e, e, Function.update_of_ne hne]

variable (hq : IsPMF q) (z₀ : α × β)

include hq in
/-- `dist` of an event of one coordinate and a function of the others. -/
lemma dist_iid_one_coordinate {τ : Type*} (i : Fin n)
    (Pf : (Fin n → α × β) → τ) (hPf : ∀ ω c, Pf (Function.update ω i c) = Pf ω) (c : α × β)
    (p : τ) :
    dist (iidPMF q n) (pair (fun ω => ω i) Pf) (c, p) = q c * dist (iidPMF q n) Pf p := by
  classical
  obtain ⟨T, hT⟩ := sum_iidPMF_mul_phi q i c fun ω => if Pf ω = p then (1 : ℝ) else 0
  have hinv : ∀ (φ : α × β → ℝ) (ω : Fin n → α × β) (c' : α × β), φ c' ≠ 0 →
      (if Pf (Function.update ω i c') = p then (1 : ℝ) else 0) =
        if Pf (Function.update ω i c) = p then 1 else 0 := fun φ ω c' _ => by
    rw [hPf, hPf]
  have h1 := hT (fun c' => if c' = c then 1 else 0) (hinv _)
  have h2 := hT (fun _ => 1) (hinv _)
  simp only [one_mul, mul_one, hq.sum_eq_one] at h2
  have e1 : dist (iidPMF q n) (pair (fun ω => ω i) Pf) (c, p) =
      ∑ ω, iidPMF q n ω * ((if ω i = c then 1 else 0) * if Pf ω = p then (1 : ℝ) else 0) := by
    simp only [dist, pair, Prod.mk.injEq]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₁ : ω i = c <;> by_cases h₂ : Pf ω = p <;> simp [h₁, h₂]
  have e2 : dist (iidPMF q n) Pf p = ∑ ω, iidPMF q n ω * if Pf ω = p then (1 : ℝ) else 0 := by
    simp only [dist]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₂ : Pf ω = p <;> simp [h₂]
  rw [e1, h1, e2, h2]
  simp

include hq in
/-- The law of one coordinate. -/
lemma dist_iid_coordinate (i : Fin n) : dist (iidPMF q n) (fun ω => ω i) = q := by
  classical
  funext c
  have h := dist_iid_one_coordinate hq i (fun _ => ()) (fun _ _ => rfl) c ()
  have e : dist (iidPMF q n) (fun _ => ()) () = 1 := by
    simp [dist, (iidPMF_isPMF hq n).sum_eq_one]
  rw [e, mul_one] at h
  rw [← h, ← sum_dist_pair_right (iidPMF q n) (fun ω => ω i) (fun _ => ()) c,
    Fintype.sum_unique]

include hq in
/-- `Zᵢ` is independent of `Zⁱ⁻¹`. -/
lemma indepRV_prefix (i : Fin n) :
    IndepRV (iidPMF q n) (fun ω => ω i) (prefixRV (seqZ z₀) i) := fun c p => by
  rw [dist_iid_one_coordinate hq i _ (prefixRV_update z₀ i) c p, dist_iid_coordinate hq i]

variable (c : HelperCode M₁ M₂ n α β)

/-- The sequence of the helper. -/
private def seqY (ω : Fin n → α × β) : Fin n → β := fun j => (ω j).2

/-- The sequence of the source. -/
private def seqX (ω : Fin n → α × β) : Fin n → α := fun j => (ω j).1

/-- The auxiliary random variable `Uᵢ = (M₂, Zⁱ⁻¹)`. -/
private def auxU (i : Fin n) (ω : Fin n → α × β) : Fin M₂ × (Fin i → α × β) :=
  (c.enc₂ (seqY ω), prefixRV (seqZ z₀) i ω)

include hq in
/-- **Lecture 11, pages 11-29 and 11-30.** For a function `M` of an i.i.d. sequence,
`∑ᵢ I(g(Zᵢ); M, Zⁱ⁻¹) ≤ log |𝓜|`, by the chain rule and the independence of `Zᵢ` and `Zⁱ⁻¹`. -/
theorem sum_mutualInfo_prefix_le {τ : Type*} [Fintype τ] (g : α × β → τ) {m : ℕ}
    (M : (Fin n → α × β) → Fin m) :
    ∑ i : Fin n, I[fun ω : Fin n → α × β => g (ω i) : pair M (prefixRV (seqZ z₀) i) ;
      iidPMF q n] ≤ log m := by
  classical
  have hμ := iidPMF_isPMF hq n
  have h1 := chain_rule_mutualInfo hμ (seqZ z₀) M n
  have h2 : I[prefixRV (seqZ z₀) n : M ; iidPMF q n] ≤ log m := by
    rw [mutualInfo_comm hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
    have h3 := entropyRV_le_log_card hμ M
    rw [Fintype.card_fin] at h3
    linarith [condEntropy_nonneg hμ M (prefixRV (seqZ z₀) n)]
  rw [h1, sum_range] at h2
  refine (sum_le_sum fun i _ => ?_).trans h2
  have hZ : seqZ z₀ (i : ℕ) = fun ω : Fin n → α × β => ω i := funext fun ω => seqZ_coe z₀ i ω
  rw [hZ]
  set Pf := prefixRV (seqZ z₀) (i : ℕ)
  have hind := (indepRV_prefix hq z₀ i).comp g id
  have h0 : I[fun ω : Fin n → α × β => g (ω i) : Pf ; iidPMF q n] = 0 :=
    (mutualInfo_eq_zero_iff hμ _ _).2 hind
  have e : I[fun ω : Fin n → α × β => g (ω i) : pair M Pf ; iidPMF q n] =
      I[fun ω : Fin n → α × β => g (ω i) : M | Pf ; iidPMF q n] := by
    have := chain_rule_mutualInfo₂ hμ (fun ω : Fin n → α × β => g (ω i)) M Pf
    rw [h0, zero_add] at this
    exact this
  rw [e, condMutualInfo_comm hμ, condMutualInfo_comm hμ (fun ω : Fin n → α × β => ω i)]
  simp only [condMutualInfo]
  have h3 := condEntropy_le_condEntropy_comp hμ M (pair (fun ω : Fin n → α × β => ω i) Pf)
    (fun w => (g w.1, w.2))
  have e2 : (fun w : (α × β) × (Fin i → α × β) => (g w.1, w.2)) ∘
      pair (fun ω : Fin n → α × β => ω i) Pf = pair (fun ω : Fin n → α × β => g (ω i)) Pf := rfl
  rw [e2] at h3
  linarith

include hq in
/-- **Lecture 11, pages 11-29 and 11-30.** `∑ᵢ I(Yᵢ; Uᵢ) ≤ log M₂`. -/
private lemma sum_info_le :
    ∑ i : Fin n, I[fun ω : Fin n → α × β => (ω i).2 : auxU z₀ c i ; iidPMF q n] ≤ log M₂ :=
  sum_mutualInfo_prefix_le hq z₀ Prod.snd fun ω => c.enc₂ (seqY ω)

include hq in
/-- **Lecture 11, page 11-30.** `∑ᵢ H(Xᵢ | Uᵢ) ≤ log M₁ + H(Xⁿ | M₁, M₂)`, and Fano's inequality. -/
private lemma sum_cond_le (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    ∑ i : Fin n, H[fun ω : Fin n → α × β => (ω i).1 | auxU z₀ c i ; iidPMF q n] ≤
      log M₁ + log 2 + c.errProb q * (n * log (Fintype.card α)) := by
  classical
  have hμ := iidPMF_isPMF hq n
  have : Nonempty (Fin M₁) := ⟨⟨0, hM₁⟩⟩
  have : Nonempty (Fin M₂) := ⟨⟨0, hM₂⟩⟩
  set M : (Fin n → α × β) → Fin M₂ := fun ω => c.enc₂ (seqY ω) with hM
  set M' : (Fin n → α × β) → Fin M₁ := fun ω => c.enc₁ (seqX ω) with hM'
  set Xk : ℕ → (Fin n → α × β) → α := fun k ω => (seqZ z₀ k ω).1 with hXk
  -- The chain rule for the source.
  have hchain := chain_rule_entropy_cond hμ Xk M n
  have hprefix : prefixRV Xk n = (seqX : (Fin n → α × β) → Fin n → α) := by
    funext ω j
    simp only [prefixRV, hXk, seqX, seqZ_coe]
  rw [hprefix, sum_range] at hchain
  -- Conditioning on more.
  have hmore : ∀ i : Fin n, H[fun ω : Fin n → α × β => (ω i).1 | auxU z₀ c i ; iidPMF q n] ≤
      H[Xk i | pair M (prefixRV Xk i) ; iidPMF q n] := fun i => by
    have hX : Xk i = fun ω : Fin n → α × β => (ω i).1 := funext fun ω => by
      simp only [hXk, seqZ_coe]
    rw [hX]
    exact condEntropy_le_condEntropy_comp hμ _ (auxU z₀ c i)
      (fun w => (w.1, fun j => (w.2 j).1))
  refine (sum_le_sum fun i _ => hmore i).trans ?_
  rw [← hchain]
  -- Fano's inequality.
  have hfano := fano_weak hμ seqX (pair M' M) c.dec
  have hcard : log (Fintype.card (Fin n → α)) = n * log (Fintype.card α) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  have herr : errProb (iidPMF q n) seqX (pair M' M) c.dec = c.errProb q := by
    have h := sum_jointIid q n fun w =>
      if c.dec (c.enc₁ (seqX w), c.enc₂ (seqY w)) ≠ seqX w then (1 : ℝ) else 0
    simp only [errProb, HelperCode.errProb, pair, hM, hM']
    have e1 : ∑ w, iidPMF q n w *
        (if c.dec (c.enc₁ (seqX w), c.enc₂ (seqY w)) ≠ seqX w then (1 : ℝ) else 0) =
        ∑ w, if c.dec (c.enc₁ (seqX w), c.enc₂ (seqY w)) ≠ seqX w then iidPMF q n w else 0 :=
      sum_congr rfl fun w _ => by split_ifs <;> simp
    rw [← e1, ← h]
    refine sum_congr rfl fun z _ => ?_
    have ex : seqX (zipSeq z.1 z.2) = z.1 := rfl
    have ey : seqY (zipSeq z.1 z.2) = z.2 := rfl
    rw [ex, ey]
    split_ifs <;> simp
  rw [herr, hcard] at hfano
  -- `H(Xⁿ | M₂) ≤ H(M₁ | M₂) + H(Xⁿ | M₁, M₂)`.
  have hc1 := chain_rule_cond hμ seqX M' M
  have hc2 := chain_rule_cond hμ M' seqX M
  have hswap : H[pair seqX M' | M ; iidPMF q n] = H[pair M' seqX | M ; iidPMF q n] :=
    condEntropy_congr_left hμ M Prod.swap Prod.swap_injective fun _ => rfl
  have h0 := condEntropy_nonneg hμ M' (pair seqX M)
  have h1 : H[M' | M ; iidPMF q n] ≤ log M₁ := by
    have h2 := condEntropy_le_entropy hμ M' M
    have h3 := entropyRV_le_log_card hμ M'
    rw [Fintype.card_fin] at h3
    linarith
  linarith

/-- **The Markov chain `Uᵢ → Yᵢ → Xᵢ` (Lecture 11, page 11-29).** The law of `((Xᵢ, Yᵢ), g(Uᵢ))`
satisfies `p(y) p(x, y, v) = p(x, y) p(y, v)`, as `Uᵢ` is a function of `Yⁿ` and `Zⁱ⁻¹`. -/
private lemma markov_auxU {τ : Type*} (i : Fin n) (g : Fin M₂ × (Fin i → α × β) → τ)
    (x : α) (y : β) (u : τ) :
    margSnd q y * dist (iidPMF q n) (pair (fun ω => ω i) fun ω => g (auxU z₀ c i ω)) ((x, y), u) =
      q (x, y) * dist (iidPMF q n) (pair (fun ω => (ω i).2) fun ω => g (auxU z₀ c i ω)) (y, u) := by
  classical
  obtain ⟨T, hT⟩ := sum_iidPMF_mul_phi q i (x, y)
    fun ω => if g (auxU z₀ c i ω) = u then (1 : ℝ) else 0
  have hinv : ∀ (ω : Fin n → α × β) (c' : α × β), c'.2 = y →
      (if g (auxU z₀ c i (Function.update ω i c')) = u then (1 : ℝ) else 0) =
        if g (auxU z₀ c i (Function.update ω i (x, y))) = u then 1 else 0 := fun ω c' hc' => by
    have e : auxU z₀ c i (Function.update ω i c') = auxU z₀ c i (Function.update ω i (x, y)) := by
      simp only [auxU, prefixRV_update]
      congr 2
      funext j
      simp only [seqY]
      by_cases hj : j = i
      · subst hj
        simp [hc']
      · simp [hj]
    rw [e]
  have h1 := hT (fun c' => if c' = (x, y) then 1 else 0) fun ω c' hne => by
    have : c' = (x, y) := by
      by_contra h
      exact hne (by simp [h])
    rw [this]
  have h2 := hT (fun c' => if c'.2 = y then 1 else 0) fun ω c' hne => by
    refine hinv ω c' ?_
    by_contra h
    exact hne (by simp [h])
  have e1 : dist (iidPMF q n) (pair (fun ω => ω i) fun ω => g (auxU z₀ c i ω)) ((x, y), u) =
      ∑ ω, iidPMF q n ω * ((if ω i = (x, y) then 1 else 0) *
        if g (auxU z₀ c i ω) = u then (1 : ℝ) else 0) := by
    simp only [dist, pair, Prod.mk.injEq]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₁ : ω i = (x, y) <;> by_cases h₂ : g (auxU z₀ c i ω) = u <;> simp [h₁, h₂]
  have e2 : dist (iidPMF q n) (pair (fun ω => (ω i).2) fun ω => g (auxU z₀ c i ω)) (y, u) =
      ∑ ω, iidPMF q n ω * ((if (ω i).2 = y then 1 else 0) *
        if g (auxU z₀ c i ω) = u then (1 : ℝ) else 0) := by
    simp only [dist, pair, Prod.mk.injEq]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₁ : (ω i).2 = y <;> by_cases h₂ : g (auxU z₀ c i ω) = u <;> simp [h₁, h₂]
  rw [e1, e2, h1, h2]
  have s1 : ∑ c' : α × β, q c' * (if c' = (x, y) then 1 else 0) = q (x, y) := by simp
  have s2 : ∑ c' : α × β, q c' * (if c'.2 = y then 1 else 0) = margSnd q y := by
    simp only [margSnd, dist, mul_ite, mul_one, mul_zero]
  rw [s1, s2]
  ring

omit [Fintype α] [Fintype β] in
lemma dist_mixLaw {Ω ι τ : Type*} [Fintype Ω] [Fintype ι] (μ : Ω → ℝ) (f : Ω × ι → τ)
    (v : τ) : dist (mixLaw μ ι) f v =
      (Fintype.card ι : ℝ)⁻¹ * ∑ i, dist μ (fun ω => f (ω, i)) v := by
  classical
  simp only [dist, mixLaw, prodDist, uniformPMF, Fintype.sum_prod_type_right, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun ω _ => ?_
  split_ifs
  · simp [mul_comm]
  · simp

include hq in
/-- **Lecture 11, pages 11-29 to 11-31.** The single-letter bounds: every code gives `p(u | y)` with
`n H(X | U) ≤ log M₁ + log 2 + Pₑ n log |𝒳|` and `n I(Y; U) ≤ log M₂`. -/
theorem HelperCode.exists_kernel_le (hn : 0 < n) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    ∃ (k : ℕ) (κ : β → Fin k → ℝ), (∀ y, IsPMF (κ y)) ∧
      n * helperCond q κ ≤ log M₁ + log 2 + c.errProb q * (n * log (Fintype.card α)) ∧
      n * helperInfo q κ ≤ log M₂ := by
  classical
  obtain ⟨z₀⟩ : Nonempty (α × β) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  have hμ := iidPMF_isPMF hq n
  have hpY := hq.dist (Prod.snd : α × β → β)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcardn : ((Fintype.card (Fin n) : ℕ) : ℝ) = n := by simp
  obtain ⟨𝒱, h𝒱⟩ : ∃ 𝒱, 𝒱 = Σ i : Fin n, Fin M₂ × (Fin i → α × β) := ⟨_, rfl⟩
  subst h𝒱
  have hne : Nonempty (Σ i : Fin n, Fin M₂ × (Fin i → α × β)) :=
    ⟨⟨⟨0, hn⟩, ⟨0, hM₂⟩, fun _ => z₀⟩⟩
  set e := Fintype.equivFin (Σ i : Fin n, Fin M₂ × (Fin i → α × β))
  have : Nonempty (Fin (Fintype.card (Σ i : Fin n, Fin M₂ × (Fin i → α × β)))) :=
    ⟨e (Classical.arbitrary _)⟩
  set ν := mixLaw (iidPMF q n) (Fin n) with hν
  have hνP : IsPMF ν := mixLaw_isPMF hμ
  set Us : (Fin n → α × β) × Fin n → Σ i : Fin n, Fin M₂ × (Fin i → α × β) :=
    fun z => ⟨z.2, auxU z₀ c z.2 z.1⟩ with hUs
  set Uq : (Fin n → α × β) × Fin n → Fin (Fintype.card _) := fun z => e (Us z) with hUq
  set Xq : (Fin n → α × β) × Fin n → α := fun z => (z.1 z.2).1 with hXq
  set Yq : (Fin n → α × β) × Fin n → β := fun z => (z.1 z.2).2 with hYq
  set r := dist ν (pair Yq Uq) with hr
  have hrP : IsPMF r := hνP.dist _
  obtain ⟨κ, hκ, hker⟩ := exists_kernel hrP
  have hYmarg : ∀ i : Fin n, dist (iidPMF q n) (fun ω : Fin n → α × β => (ω i).2) = margSnd q :=
    fun i => by
      have h := dist_comp_eq (iidPMF q n) (fun ω : Fin n → α × β => ω i) Prod.snd
      rwa [dist_iid_coordinate hq i] at h
  have hYq : dist ν Yq = margSnd q := by
    funext y
    rw [dist_mixLaw]
    simp only [hYq, hYmarg, Finset.sum_const, card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by simp [hn'.ne']), one_mul]
  have hrfst : dist r Prod.fst = margSnd q := by
    rw [hr, ← dist_comp_eq]
    exact hYq
  have hker' : ∀ y u, r (y, u) = margSnd q y * κ y u := fun y u => by
    rw [hker, hrfst]
  -- The Markov chain under `ν`.
  have hmark : ∀ x y u, margSnd q y * dist ν (pair (fun z => z.1 z.2) Uq) ((x, y), u) =
      q (x, y) * r (y, u) := fun x y u => by
    rw [hr, dist_mixLaw, dist_mixLaw, mul_left_comm, mul_left_comm (q (x, y))]
    congr 1
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun i _ => markov_auxU z₀ c i (fun w => e ⟨i, w⟩) x y u
  -- The law of `((X, Y), U)`.
  have hLaw : helperLaw q κ = dist ν (pair (fun z => z.1 z.2) Uq) := by
    funext ⟨⟨x, y⟩, u⟩
    simp only [helperLaw, jointOf]
    by_cases hpy : margSnd q y = 0
    · have hq0 : q (x, y) = 0 := by
        have h1 : ∑ a, q (a, y) = 0 := by rw [← hpy]; exact (dist_snd q y).symm
        exact (sum_eq_zero_iff_of_nonneg fun a _ => hq.nonneg _).1 h1 x (mem_univ x)
      have hle : dist ν (pair (fun z => z.1 z.2) Uq) ((x, y), u) ≤ dist ν Yq y := by
        simp only [dist]
        refine sum_le_sum fun z _ => ?_
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact absurd (congrArg (fun w => w.1.2) h1) h2
        · exact hνP.nonneg z
        · exact le_rfl
      rw [hYq, hpy] at hle
      have h0 := (hνP.dist (pair (fun z : (Fin n → α × β) × Fin n => z.1 z.2) Uq)).nonneg
        ((x, y), u)
      rw [hq0, zero_mul]
      exact (le_antisymm hle h0).symm
    · have h1 := hmark x y u
      rw [hker' y u] at h1
      have h2 : margSnd q y * dist ν (pair (fun z => z.1 z.2) Uq) ((x, y), u) =
          margSnd q y * (q (x, y) * κ y u) := by
        rw [h1]
        ring
      exact (mul_left_cancel₀ hpy h2).symm
  have hLawP := helperLaw_isPMF hq hκ
  -- The two informations.
  have hC : helperCond q κ = (n : ℝ)⁻¹ * ∑ i : Fin n,
      H[fun ω : Fin n → α × β => (ω i).1 | auxU z₀ c i ; iidPMF q n] := by
    have e1 : helperCond q κ = H[Xq | Uq ; ν] := by
      refine condEntropy_eq_of_dist_pair_eq hLawP hνP ?_
      rw [hLaw, ← dist_comp_eq]
      rfl
    have e2 : H[Xq | Uq ; ν] = H[Xq | Us ; ν] :=
      condEntropy_comp_right_injective hνP Xq Us e.injective
    have e3 := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α × β) => (ω i).1)
      fun i => auxU z₀ c i
    rw [hcardn] at e3
    rw [e1, e2]
    exact e3
  have hIs : ∑ i : Fin n, H[fun ω : Fin n → α × β => (ω i).2 ; iidPMF q n] =
      n * entropy (margSnd q) := by
    simp only [entropyRV, hYmarg, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hI : helperInfo q κ = entropy (margSnd q) - (n : ℝ)⁻¹ * ∑ i : Fin n,
      H[fun ω : Fin n → α × β => (ω i).2 | auxU z₀ c i ; iidPMF q n] := by
    have e1 : helperInfo q κ = I[Yq : Uq ; ν] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [hLaw, ← dist_comp_eq]
      rfl
    have e2 : I[Yq : Uq ; ν] = I[Yq : Us ; ν] :=
      mutualInfo_congr_right hνP Yq e e.injective fun _ => rfl
    have e3 := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α × β) => (ω i).2)
      fun i => auxU z₀ c i
    rw [hcardn] at e3
    rw [e1, e2, mutualInfo_eq_entropy_sub_condEntropy hνP, entropyRV, hYq]
    congr 1
  refine ⟨_, κ, hκ, ?_, ?_⟩
  · rw [hC, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
    exact sum_cond_le hq z₀ c hM₁ hM₂
  · have hb := sum_info_le hq z₀ c
    have hexp : ∑ i : Fin n, I[fun ω : Fin n → α × β => (ω i).2 : auxU z₀ c i ; iidPMF q n] =
        n * entropy (margSnd q) - ∑ i : Fin n,
          H[fun ω : Fin n → α × β => (ω i).2 | auxU z₀ c i ; iidPMF q n] := by
      rw [← hIs, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ => mutualInfo_eq_entropy_sub_condEntropy hμ _ _
    rw [hexp] at hb
    rw [hI, mul_sub, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
    exact hb

end Converse

/-! ### Theorem 2 -/

section Theorem

variable {α β : Type*} [Fintype α] [Fintype β] {q : α × β → ℝ}

/-- A rate pair given by `p(u | y)` with `U` on any finite type is in the region, where `U` is on
`Fin k`. -/
theorem mem_helperRegionBits_of_kernel {𝒰 : Type*} [Fintype 𝒰] (hq : IsPMF q)
    {κ : β → 𝒰 → ℝ} (hκ : ∀ y, IsPMF (κ y)) {R₁ R₂ : ℝ} (h₁ : helperCond q κ / log 2 ≤ R₁)
    (h₂ : helperInfo q κ / log 2 ≤ R₂) : (R₁, R₂) ∈ helperRegionBits q := by
  classical
  set e := Fintype.equivFin 𝒰
  set κ' : β → Fin (Fintype.card 𝒰) → ℝ := fun y k => κ y (e.symm k)
  have hκ' : ∀ y, IsPMF (κ' y) := fun y =>
    ⟨fun k => (hκ y).nonneg _, by rw [e.symm.sum_comp (κ y), (hκ y).sum_eq_one]⟩
  have hP := helperLaw_isPMF hq hκ
  have hP' := helperLaw_isPMF hq hκ'
  set T : (α × β) × Fin (Fintype.card 𝒰) ≃ (α × β) × 𝒰 := (Equiv.refl _).prodCongr e.symm
  have hlaw : helperLaw q κ' = fun z => helperLaw q κ (T z) := rfl
  have hC : helperCond q κ' = helperCond q κ := by
    have e1 : helperCond q κ' =
        H[fun z : (α × β) × 𝒰 => z.1.1 | fun z => e z.2 ; helperLaw q κ] := by
      refine condEntropy_eq_of_dist_pair_eq hP' hP ?_
      have h := dist_comp_equiv' T (helperLaw q κ) (pair (fun z => e z.2) fun z => z.1.1)
      rw [← h, hlaw]
      congr 1
      funext z
      simp [T, pair]
    rw [e1]
    exact condEntropy_comp_right_injective hP _ Prod.snd e.injective
  have hI : helperInfo q κ' = helperInfo q κ := by
    have e1 : helperInfo q κ' =
        I[fun z : (α × β) × 𝒰 => z.1.2 : fun z => e z.2 ; helperLaw q κ] := by
      refine mutualInfo_eq_of_dist_pair_eq ?_
      have h := dist_comp_equiv' T (helperLaw q κ) (pair (fun z => z.1.2) fun z => e z.2)
      rw [← h, hlaw]
      congr 1
      funext z
      simp [T, pair]
    rw [e1]
    exact mutualInfo_congr_right hP _ e e.injective fun _ => rfl
  exact ⟨_, κ', hκ', by rwa [hC], by rwa [hI]⟩

/-- **The converse of Theorem 2 of Lecture 11.** -/
theorem IsAchievableHelperBits.mem_closure_helperRegionBits (hq : IsPMF q) {R₁ R₂ : ℝ}
    (h : IsAchievableHelperBits q R₁ R₂) : (R₁, R₂) ∈ closure (helperRegionBits q) := by
  obtain ⟨h₁, h₂, c, hc⟩ := h
  have hl := log_pos one_lt_two
  set A := log (Fintype.card α)
  set ε : ℕ → ℝ := fun n => (log 2 / n + (c n).errProb q * A) / log 2 with hε
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have t := ((tendsto_const_div_atTop_nhds_zero_nat (log 2)).add (hc.mul_const A)).div_const
      (log 2)
    simpa [hε] using t
  have hlim : Tendsto (fun n => (R₁ + ε n, R₂)) atTop (𝓝 (R₁, R₂)) := by
    have t := (tendsto_const_nhds (x := R₁)).add hεlim
    rw [add_zero] at t
    exact t.prodMk_nhds tendsto_const_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨k, κ, hκ, b₁, b₂⟩ := (c n).exists_kernel_le hq hn (by positivity) (by positivity)
  have l₁ := log_two_pow_floor_le n h₁
  have l₂ := log_two_pow_floor_le n h₂
  refine ⟨k, κ, hκ, ?_, ?_⟩
  · simp only
    rw [div_le_iff₀ hl]
    have h3 : (n : ℝ) * helperCond q κ ≤ n * (R₁ * log 2) + log 2 + (c n).errProb q * (n * A) := by
      linarith
    have e : (R₁ + ε n) * log 2 = R₁ * log 2 + (log 2 / n + (c n).errProb q * A) := by
      simp only [hε]
      field_simp
    rw [e]
    refine le_of_mul_le_mul_left ?_ hn'
    calc (n : ℝ) * helperCond q κ ≤ _ := h3
      _ = _ := by
        field_simp
        ring
  · simp only
    rw [div_le_iff₀ hl]
    exact le_of_mul_le_mul_left (b₂.trans l₂) hn'

/-- **Theorem 2 of Lecture 11 of [elgamal2010], page 11-23.** The optimal rate region for lossless
source coding with a helper is `R₁ ≥ H(X | U)`, `R₂ ≥ I(Y; U)` for some `p(u | y)`, up to closure,
as the cardinality of `U` is not bounded. -/
theorem helperOptimalRegionBits_eq (hq : IsPMF q) :
    helperOptimalRegionBits q = closure (helperRegionBits q) := by
  refine Set.Subset.antisymm (closure_minimal (fun R hR => ?_) isClosed_closure)
    (closure_minimal ?_ isClosed_closure)
  · exact IsAchievableHelperBits.mem_closure_helperRegionBits hq hR
  · rintro ⟨R₁, R₂⟩ ⟨k, κ, hκ, h₁, h₂⟩
    dsimp only at h₁ h₂
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ => (R₁ + 1 / ((n : ℝ) + 1), R₂ + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 (R₁, R₂)) := by
      have l₁ := (tendsto_const_nhds (x := R₁)).add ht
      have l₂ := (tendsto_const_nhds (x := R₂)).add ht
      rw [add_zero] at l₁ l₂
      exact l₁.prodMk_nhds l₂
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact isAchievableHelperBits_of_lt hq hκ (by linarith) (by linarith)

end Theorem

end InfoTheory
