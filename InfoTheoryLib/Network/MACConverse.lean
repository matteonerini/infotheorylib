/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.StochasticProcess.HiddenMarkov
public import InfoTheoryLib.Network.MACCode
public import InfoTheoryLib.Network.MACRegion

/-!
# The multiple-access channel: converse

Every achievable rate pair of a multiple-access channel lies in the closure of the region
`R₁ ≤ I(X₁; Y | X₂, Q)`, `R₂ ≤ I(X₂; Y | X₁, Q)`, `R₁ + R₂ ≤ I(X₁, X₂; Y | Q)` (Section 15.3.4).
For a code with independent uniform messages `W₁`, `W₂`, Fano's inequality bounds `H(W₁, W₂ | Yⁿ)`,
and the memoryless channel gives `I(W₁; Yⁿ | W₂) ≤ ∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ)` and
`I(W₁, W₂; Yⁿ) ≤ ∑ᵢ I(X₁ᵢ, X₂ᵢ; Yᵢ)`, (15.97)–(15.125). Since `W₁` and `W₂` are independent, so are
`X₁ᵢ(W₁)` and `X₂ᵢ(W₂)`, and the `i`-th terms are the mutual informations of the product input
distribution of column `i` of the codebooks; the time-sharing variable `Q` is uniform on the `n`
columns, (15.126)–(15.130).

## Main definitions

* `codeLaw ν W x`: the joint law `ν(w) p(yⁿ | xⁿ(w))` of a message and the output of a memoryless
  channel without feedback.
* `MACCode.jointLaw W c`: the joint law of the messages `(W₁, W₂)` and the output for a
  multiple-access code, (15.97).
* `MACCode.letterDist₁ c i`, `MACCode.letterDist₂ c i`: the empirical distributions of column `i`
  of the codebooks.

## Main statements

* `condEntropy_codeLaw`: (15.109)–(15.110), `H(Yⁿ | W) = ∑ᵢ H(Yᵢ | Xᵢ)` for a memoryless channel.
* `condEntropy_pi_le_sum`: `H(Yⁿ | Z) ≤ ∑ᵢ H(Yᵢ | Z)`.
* `condMutualInfo_comp`: information quantities of functions of `V` only depend on the law
  of `V`.
* `MACCode.log_le_macInfo₁`, `MACCode.log_le_macInfo₂`, `MACCode.log_mul_le_macInfo₁₂`:
  (15.101)–(15.125) for a single code.
* `IsAchievableMAC.mem_closure_macRegion`: **Theorems 15.3.1 and 15.3.4 (converse)**.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 15.3.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Transferring information quantities along a common joint law -/

section Transfer

variable {Ω T α β γ : Type*} [Fintype Ω] [Fintype T] [Fintype α] [Fintype β] [Fintype γ]
  {μ : Ω → ℝ}

/-- Information quantities of functions of `V` only depend on the law of `V`. -/
lemma mutualInfo_comp (V : Ω → T) (f : T → α) (g : T → β) :
    I[f ∘ V : g ∘ V ; μ] = I[f : g ; dist μ V] :=
  mutualInfo_eq_of_dist_pair_eq (dist_comp_eq μ V (pair f g))

lemma condEntropy_comp_comp (hμ : IsPMF μ) (V : Ω → T) (f : T → α) (h : T → γ) :
    H[f ∘ V | h ∘ V ; μ] = H[f | h ; dist μ V] :=
  condEntropy_eq_of_dist_pair_eq hμ (hμ.dist V) (dist_comp_eq μ V (pair h f))

lemma condMutualInfo_comp (hμ : IsPMF μ) (V : Ω → T) (f : T → α) (g : T → β) (h : T → γ) :
    I[f ∘ V : g ∘ V | h ∘ V ; μ] = I[f : g | h ; dist μ V] := by
  unfold condMutualInfo
  rw [condEntropy_comp_comp hμ V f h]
  exact congrArg _ (condEntropy_comp_comp hμ V f (pair g h))

/-- **Subadditivity of conditional entropy.** `H(Y₁, …, Yₙ | Z) ≤ ∑ᵢ H(Yᵢ | Z)`. -/
theorem condEntropy_pi_le_sum (hμ : IsPMF μ) {n : ℕ} (Y : Ω → Fin n → β) (Z : Ω → γ) :
    H[Y | Z ; μ] ≤ ∑ i, H[fun ω => Y ω i | Z ; μ] := by
  induction n with
  | zero =>
    have h1 := condEntropy_le_entropy hμ Y Z
    have h2 := entropyRV_le_log_card hμ Y
    simp only [Fintype.card_unique, Nat.cast_one, log_one] at h2
    simp only [univ_eq_empty, sum_empty]
    linarith
  | succ n ih =>
    have e : H[Y | Z ; μ] =
        H[pair (fun ω => Fin.init (Y ω)) (fun ω => Y ω (Fin.last n)) | Z ; μ] :=
      (condEntropy_congr_left hμ Z (fun v => (Fin.init v, v (Fin.last n)))
        (fun a b h => by
          simp only [Prod.mk.injEq] at h
          rw [← Fin.snoc_init_self a, ← Fin.snoc_init_self b, h.1, h.2]) fun _ => rfl).symm
    rw [e, chain_rule_cond hμ, Fin.sum_univ_castSucc]
    have h1 := condEntropy_le_condEntropy hμ (fun ω => Y ω (Fin.last n))
      (fun ω => Fin.init (Y ω)) Z
    have h2 := ih (fun ω => Fin.init (Y ω))
    exact add_le_add h2 h1

end Transfer

/-! ### The law of a code on a memoryless channel -/

section CodeLaw

variable {𝒲 α β : Type*} [Fintype 𝒲] [Fintype α] [Fintype β]

omit [Fintype 𝒲] [Fintype α] in
/-- `∑_{yⁿ} ∏ₖ pₖ(yₖ) g(yᵢ) = ∑_b pᵢ(b) g(b)`: the `i`-th marginal of a product of pmfs. -/
lemma sum_prod_mul_apply {n : ℕ} {p : Fin n → β → ℝ} (hp : ∀ k, ∑ b, p k b = 1) (i : Fin n)
    (g : β → ℝ) : ∑ y : Fin n → β, (∏ k, p k (y k)) * g (y i) = ∑ b, p i b * g b := by
  classical
  have h := (Fintype.prod_sum fun k b => if k = i then p k b * g b else p k b).symm
  have h1 : ∀ y : Fin n → β, (∏ k, if k = i then p k (y k) * g (y k) else p k (y k)) =
      (∏ k, p k (y k)) * g (y i) := by
    intro y
    rw [← mul_prod_erase univ _ (mem_univ i), ← mul_prod_erase univ (fun k => p k (y k))
      (mem_univ i)]
    simp only [↓reduceIte]
    rw [prod_congr rfl fun k hk =>
      (show (if k = i then p k (y k) * g (y k) else p k (y k)) = p k (y k) by
        simp [ne_of_mem_erase hk])]
    ring
  have h2 : ∀ k, (∑ b, if k = i then p k b * g b else p k b) =
      if k = i then ∑ b, p i b * g b else 1 := by
    intro k
    split_ifs with hk
    · subst hk; rfl
    · exact hp k
  simp only [h1, h2] at h
  rw [h]
  simp

omit [Fintype α] in
/-- The entropy of a product of pmfs is the sum of their entropies. -/
lemma entropy_prod_pmf {n : ℕ} {p : Fin n → β → ℝ} (hp : ∀ k, IsPMF (p k)) :
    entropy (fun y : Fin n → β => ∏ k, p k (y k)) = ∑ k, entropy (p k) := by
  unfold entropy
  have h : ∀ y : Fin n → β, (∏ k, p k (y k)) * log (∏ k, p k (y k)) =
      ∑ k, (∏ j, p j (y j)) * log (p k (y k)) := by
    intro y
    by_cases h0 : ∏ k, p k (y k) = 0
    · simp [h0]
    · rw [log_prod (fun k _ => (prod_ne_zero_iff.1 h0) k (mem_univ k)), mul_sum]
  simp_rw [h]
  rw [sum_comm, ← sum_neg_distrib]
  exact sum_congr rfl fun k _ => by
    rw [sum_prod_mul_apply (fun k => (hp k).sum_eq_one) k (fun b => log (p k b))]

/-- The joint law `ν(w) p(yⁿ | xⁿ(w))` of a message with prior `ν`, sent with the codewords `x`,
and the output of `n` uses of the memoryless channel `W` without feedback. -/
def codeLaw (ν : 𝒲 → ℝ) (W : α → β → ℝ) {n : ℕ} (x : 𝒲 → Fin n → α) :
    𝒲 × (Fin n → β) → ℝ :=
  fun z => ν z.1 * channelExt W n (x z.1) z.2

variable {ν : 𝒲 → ℝ} {W : α → β → ℝ} {n : ℕ} {x : 𝒲 → Fin n → α}

omit [Fintype α] in
lemma codeLaw_isPMF (hν : IsPMF ν) (hW : IsChannel W) : IsPMF (codeLaw ν W x) := by
  refine ⟨fun z => mul_nonneg (hν.nonneg _) (channelExt_nonneg hW _ _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [codeLaw, ← mul_sum, ((hW.ext n) _).sum_eq_one, mul_one]
  exact hν.sum_eq_one

omit [Fintype α] in
lemma dist_codeLaw_comp_fst (hW : IsChannel W) {γ : Type*} (F : 𝒲 → γ) :
    dist (codeLaw ν W x) (F ∘ Prod.fst) = dist ν F := by
  rw [dist_comp_eq]
  congr 1
  funext w
  rw [dist_fst]
  simp only [codeLaw, ← mul_sum, ((hW.ext n) _).sum_eq_one, mul_one]

omit [Fintype α] in
/-- **(15.110)** Given a function `F(W)` that determines the `i`-th input `xᵢ(W) = f(F(W))`, the
`i`-th output is produced by the channel from `f(F(W))`. -/
lemma dist_codeLaw_letter (hW : IsChannel W) {γ : Type*} (F : 𝒲 → γ) (f : γ → α)
    (i : Fin n) (hF : ∀ w, x w i = f (F w)) (c : γ) (b : β) :
    dist (codeLaw ν W x) (pair (F ∘ Prod.fst) (fun z => z.2 i)) (c, b) =
      dist (codeLaw ν W x) (F ∘ Prod.fst) c * W (f c) b := by
  classical
  rw [dist_codeLaw_comp_fst hW]
  simp only [dist, pair, Function.comp, Prod.mk.injEq, Fintype.sum_prod_type, codeLaw]
  rw [sum_mul]
  refine sum_congr rfl fun w _ => ?_
  by_cases hw : F w = c
  · simp only [hw, true_and, ↓reduceIte]
    have := sum_prod_mul_apply (p := fun k => W (x w k)) (fun k => (hW _).sum_eq_one) i
      (fun b' => if b' = b then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte] at this
    rw [← hw, ← hF w, ← this, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [channelExt]
  · simp [hw]

/-- **(15.109)–(15.110)** For a memoryless channel without feedback, `H(Yⁿ | W) = ∑ᵢ H(Yᵢ | Xᵢ)`. -/
theorem condEntropy_codeLaw (hW : IsChannel W) :
    H[Prod.snd | Prod.fst ; codeLaw ν W x] =
      ∑ i, H[fun z => z.2 i | fun z => x z.1 i ; codeLaw ν W x] := by
  set μ := codeLaw ν W x
  have hfst : dist μ Prod.fst = ν := by
    have := dist_codeLaw_comp_fst (ν := ν) (x := x) hW id
    rw [dist_id] at this
    exact this
  have hch : ∀ w y, dist μ (pair Prod.fst Prod.snd) (w, y) =
      dist μ Prod.fst w * channelExt W n (x w) y := by
    intro w y
    rw [dist_pair_fst_snd, hfst]
    rfl
  rw [condEntropy_of_channel x hch]
  have hent : ∀ xs : Fin n → α, entropy (channelExt W n xs) = ∑ i, entropy (W (xs i)) :=
    fun xs => entropy_prod_pmf (p := fun k => W (xs k)) fun k => hW _
  simp only [hent, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_dist_mul_comp (fun xs : Fin n → α => xs i) μ (x ∘ Prod.fst) (fun a => entropy (W a))]
  have hch' := dist_codeLaw_letter (ν := ν) hW (fun w => x w i) id i (fun w => rfl)
  rw [show (fun z : 𝒲 × (Fin n → β) => x z.1 i) = (fun w => x w i) ∘ Prod.fst from rfl,
    condEntropy_of_channel id hch']
  rfl

end CodeLaw

/-! ### The joint law of a multiple-access code -/

variable {α₁ α₂ β : Type*} [Fintype α₁] [Fintype α₂] [Fintype β]

namespace MACCode

variable {M₁ M₂ n : ℕ} (W : α₁ × α₂ → β → ℝ) (c : MACCode M₁ M₂ n α₁ α₂ β)

/-- **(15.97)** The joint law of independent uniform messages `(W₁, W₂)` and the output. -/
def jointLaw : (Fin M₁ × Fin M₂) × (Fin n → β) → ℝ :=
  codeLaw (uniformPMF (Fin M₁ × Fin M₂)) W fun w => c.input w.1 w.2

/-- The empirical distribution of the symbols in column `i` of the first codebook: the law of
`X₁ᵢ(W₁)`. -/
def letterDist₁ (i : Fin n) : α₁ → ℝ := dist (uniformPMF (Fin M₁)) fun w => c.enc₁ w i

/-- The empirical distribution of the symbols in column `i` of the second codebook: the law of
`X₂ᵢ(W₂)`. -/
def letterDist₂ (i : Fin n) : α₂ → ℝ := dist (uniformPMF (Fin M₂)) fun w => c.enc₂ w i

variable {W}

omit [Fintype α₁] [Fintype α₂] in
lemma jointLaw_isPMF (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂) : IsPMF (c.jointLaw W) :=
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  codeLaw_isPMF uniformPMF_isPMF hW

omit [Fintype α₂] [Fintype β] in
lemma letterDist₁_isPMF (h₁ : 0 < M₁) (i : Fin n) : IsPMF (c.letterDist₁ i) :=
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  uniformPMF_isPMF.dist _

omit [Fintype α₁] [Fintype β] in
lemma letterDist₂_isPMF (h₂ : 0 < M₂) (i : Fin n) : IsPMF (c.letterDist₂ i) :=
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  uniformPMF_isPMF.dist _

omit [Fintype α₁] [Fintype α₂] in
lemma dist_jointLaw_comp_fst (hW : IsChannel W) {γ : Type*} (F : Fin M₁ × Fin M₂ → γ) :
    dist (c.jointLaw W) (F ∘ Prod.fst) = dist (uniformPMF (Fin M₁ × Fin M₂)) F :=
  dist_codeLaw_comp_fst hW F

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma dist_uniformPMF_prod_fst {γ : Type*} (h₂ : 0 < M₂) (g : Fin M₁ → γ) :
    dist (uniformPMF (Fin M₁ × Fin M₂)) (fun w => g w.1) = dist (uniformPMF (Fin M₁)) g := by
  classical
  funext a
  simp only [dist, uniformPMF, Fintype.card_prod, Fintype.card_fin, Fintype.sum_prod_type]
  refine sum_congr rfl fun w _ => ?_
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  split_ifs
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · simp

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
lemma dist_uniformPMF_prod_snd {γ : Type*} (h₁ : 0 < M₁) (g : Fin M₂ → γ) :
    dist (uniformPMF (Fin M₁ × Fin M₂)) (fun w => g w.2) = dist (uniformPMF (Fin M₂)) g := by
  classical
  funext a
  simp only [dist, uniformPMF, Fintype.card_prod, Fintype.card_fin, Fintype.sum_prod_type]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  split_ifs
  · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · simp

omit [Fintype α₁] [Fintype α₂] [Fintype β] in
/-- **(15.130)** Independent messages give independent letters:
`Pr{X₁ᵢ = x₁, X₂ᵢ = x₂} = Pr{X₁ᵢ = x₁} Pr{X₂ᵢ = x₂}`. -/
lemma dist_uniformPMF_prod_pair {γ δ : Type*} (g : Fin M₁ → γ)
    (g' : Fin M₂ → δ) :
    dist (uniformPMF (Fin M₁ × Fin M₂)) (fun w => (g w.1, g' w.2)) =
      prodDist (dist (uniformPMF (Fin M₁)) g) (dist (uniformPMF (Fin M₂)) g') := by
  classical
  funext ⟨a, b⟩
  simp only [dist, uniformPMF, prodDist, Fintype.card_prod, Fintype.card_fin,
    Fintype.sum_prod_type, Prod.mk.injEq]
  rw [sum_mul_sum]
  refine sum_congr rfl fun w _ => sum_congr rfl fun w' _ => ?_
  by_cases ha : g w = a <;> by_cases hb : g' w' = b <;> simp [ha, hb]
  ring

omit [Fintype α₁] [Fintype α₂] in
/-- The law of `((X₁ᵢ, X₂ᵢ), Yᵢ)` is `p₁ᵢ(x₁) p₂ᵢ(x₂) p(y | x₁, x₂)`, with the empirical
distributions of column `i`. -/
lemma dist_jointLaw_letter (hW : IsChannel W) (i : Fin n) :
    dist (c.jointLaw W) (fun z => ((c.enc₁ z.1.1 i, c.enc₂ z.1.2 i), z.2 i)) =
      macJoint (c.letterDist₁ i) (c.letterDist₂ i) W := by
  funext ⟨u, b⟩
  have h : dist (c.jointLaw W) (pair ((fun w : Fin M₁ × Fin M₂ => (c.enc₁ w.1 i, c.enc₂ w.2 i)) ∘
      Prod.fst) (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.2 i)) (u, b) = dist (c.jointLaw W)
      ((fun w : Fin M₁ × Fin M₂ => (c.enc₁ w.1 i, c.enc₂ w.2 i)) ∘ Prod.fst) u * W u b :=
    dist_codeLaw_letter (ν := uniformPMF (Fin M₁ × Fin M₂))
      (x := fun w => c.input w.1 w.2) hW (fun w => (c.enc₁ w.1 i, c.enc₂ w.2 i)) id i
      (fun w => rfl) u b
  have hX : dist (c.jointLaw W) ((fun w : Fin M₁ × Fin M₂ => (c.enc₁ w.1 i, c.enc₂ w.2 i)) ∘
      Prod.fst) = prodDist (c.letterDist₁ i) (c.letterDist₂ i) := by
    rw [dist_jointLaw_comp_fst c hW]
    exact dist_uniformPMF_prod_pair (fun w => c.enc₁ w i) (fun w => c.enc₂ w i)
  have e : (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => ((c.enc₁ z.1.1 i, c.enc₂ z.1.2 i), z.2 i)) =
      pair ((fun w : Fin M₁ × Fin M₂ => (c.enc₁ w.1 i, c.enc₂ w.2 i)) ∘ Prod.fst)
        (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.2 i) := rfl
  rw [e, h, hX]
  rfl

omit [Fintype α₁] [Fintype α₂] in
/-- **(15.55)** With uniform messages, `Pr{g(Yⁿ) ≠ (W₁, W₂)} = Pₑ^(n)`. -/
lemma errProb_jointLaw (h₁ : 0 < M₁) (h₂ : 0 < M₂) :
    errProb (c.jointLaw W) Prod.fst Prod.snd c.dec = c.avgErrProb W := by
  classical
  have hM : ((M₁ * M₂ : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [errProb, Fintype.sum_prod_type, jointLaw, codeLaw, uniformPMF, Fintype.card_prod,
    Fintype.card_fin, avgErrProb, condErrProb]
  rw [sum_div]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_div]
  refine sum_congr rfl fun y _ => ?_
  push_cast
  split_ifs <;> ring

/-! ### The bounds for a single code -/

section Bounds

variable (hW : IsChannel W) (h₁ : 0 < M₁) (h₂ : 0 < M₂)
include hW h₁ h₂

omit [Fintype α₁] [Fintype α₂] in
/-- **(15.98)** Fano's inequality: `H(W₁, W₂ | Yⁿ) ≤ log 2 + Pₑ^(n) log (M₁ M₂)`. -/
lemma condEntropy_msg_le :
    H[Prod.fst | Prod.snd ; c.jointLaw W] ≤ log 2 + c.avgErrProb W * log (M₁ * M₂) := by
  have h := fano_weak (c.jointLaw_isPMF hW h₁ h₂)
    (Prod.fst : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₁ × Fin M₂) Prod.snd c.dec
  rw [c.errProb_jointLaw h₁ h₂, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  push_cast at h
  exact h

omit h₁ h₂ in
/-- **(15.109)–(15.110)** `H(Yⁿ | W₁, W₂) = ∑ᵢ H(Yᵢ | X₁ᵢ, X₂ᵢ)`. -/
lemma condEntropy_out_msg :
    H[Prod.snd | Prod.fst ; c.jointLaw W] =
      ∑ i, H[fun z => z.2 i | fun z => (c.enc₁ z.1.1 i, c.enc₂ z.1.2 i) ; c.jointLaw W] :=
  condEntropy_codeLaw hW

omit [Fintype α₁] [Fintype α₂] in
lemma entropy_msg : H[Prod.fst ; c.jointLaw W] = log (M₁ * M₂) := by
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, h₁⟩, ⟨0, h₂⟩)⟩
  have hd := c.dist_jointLaw_comp_fst hW (id : Fin M₁ × Fin M₂ → Fin M₁ × Fin M₂)
  rw [dist_id] at hd
  rw [entropyRV, show (Prod.fst : (Fin M₁ × Fin M₂) × (Fin n → β) → _) = id ∘ Prod.fst from rfl,
    hd, entropy_uniformPMF, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rfl

omit [Fintype α₁] [Fintype α₂] in
lemma entropy_msg₁ : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1 ; c.jointLaw W] =
    log M₁ := by
  have : Nonempty (Fin M₁) := ⟨⟨0, h₁⟩⟩
  have hd := c.dist_jointLaw_comp_fst hW (fun w : Fin M₁ × Fin M₂ => w.1)
  have hu : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.1) = uniformPMF (Fin M₁) := by
    have := dist_uniformPMF_prod_fst (M₁ := M₁) h₂ id
    rw [dist_id] at this
    exact this
  rw [hu] at hd
  rw [entropyRV, show (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.1) =
    (fun w : Fin M₁ × Fin M₂ => w.1) ∘ Prod.fst from rfl, hd, entropy_uniformPMF,
    Fintype.card_fin]

omit [Fintype α₁] [Fintype α₂] in
lemma entropy_msg₂ : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2 ; c.jointLaw W] =
    log M₂ := by
  have : Nonempty (Fin M₂) := ⟨⟨0, h₂⟩⟩
  have hd := c.dist_jointLaw_comp_fst hW (fun w : Fin M₁ × Fin M₂ => w.2)
  have hu : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.2) = uniformPMF (Fin M₂) := by
    have := dist_uniformPMF_prod_snd (M₂ := M₂) h₁ id
    rw [dist_id] at this
    exact this
  rw [hu] at hd
  rw [entropyRV, show (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.1.2) =
    (fun w : Fin M₁ × Fin M₂ => w.2) ∘ Prod.fst from rfl, hd, entropy_uniformPMF,
    Fintype.card_fin]

/-- **(15.101)–(15.114)** `log M₁ ≤ ∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ) + log 2 + Pₑ^(n) log (M₁ M₂)`. -/
theorem log_le_macInfo₁ :
    log M₁ ≤ ∑ i, macInfo₁ (c.letterDist₁ i) (c.letterDist₂ i) W + log 2 +
      c.avgErrProb W * log (M₁ * M₂) := by
  set μ := c.jointLaw W
  have hμ : IsPMF μ := c.jointLaw_isPMF hW h₁ h₂
  set Wv : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₁ × Fin M₂ := Prod.fst
  set W₁ : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₁ := fun z => z.1.1
  set W₂ : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₂ := fun z => z.1.2
  set Y : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin n → β := Prod.snd
  -- `log M₁ = H(W₁ | W₂)`.
  have hH : H[W₁ | W₂ ; μ] = log M₁ := by
    rw [condEntropy_eq_sub hμ]
    have e : H[pair W₂ W₁ ; μ] = H[Wv ; μ] :=
      entropyRV_eq_of_injective μ Prod.swap Prod.swap_injective fun _ => rfl
    rw [e, c.entropy_msg hW h₁ h₂, c.entropy_msg₂ hW h₁ h₂,
      log_mul (by positivity) (by positivity)]
    ring
  -- `H(W₁ | Yⁿ, W₂) ≤ H(W₁, W₂ | Yⁿ)`, (15.99).
  have hF : H[W₁ | pair Y W₂ ; μ] ≤ log 2 + c.avgErrProb W * log (M₁ * M₂) := by
    have e : H[W₁ | pair Y W₂ ; μ] = H[W₁ | pair W₂ Y ; μ] :=
      condEntropy_congr_right hμ W₁ Prod.swap Prod.swap_injective fun _ => rfl
    have h1 := condEntropy_le_condEntropy hμ W₁ W₂ Y
    have h2 := condEntropy_comp_le hμ Wv Y Prod.fst
    have h3 := c.condEntropy_msg_le hW h₁ h₂
    rw [e]
    exact h1.trans (h2.trans h3)
  -- `I(W₁; Yⁿ | W₂) = H(Yⁿ | W₂) - H(Yⁿ | W₁, W₂)`, (15.105)–(15.108).
  have hI : I[W₁ : Y | W₂ ; μ] = H[Y | W₂ ; μ] - H[Y | Wv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
    rfl
  -- (15.109)–(15.112).
  have hY : H[Y | W₂ ; μ] ≤ ∑ i, H[fun z => z.2 i |
      fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => c.enc₂ z.1.2 i ; μ] :=
    (condEntropy_pi_le_sum hμ Y W₂).trans (sum_le_sum fun i _ =>
      condEntropy_le_condEntropy_comp hμ _ W₂ (fun w => c.enc₂ w i))
  have hterm : ∀ i, H[fun z => z.2 i | fun z : (Fin M₁ × Fin M₂) × (Fin n → β) =>
      c.enc₂ z.1.2 i ; μ] - H[fun z => z.2 i | fun z => (c.enc₁ z.1.1 i, c.enc₂ z.1.2 i) ; μ] =
      macInfo₁ (c.letterDist₁ i) (c.letterDist₂ i) W := by
    intro i
    have e1 := condMutualInfo_comp hμ
      (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => ((c.enc₁ z.1.1 i, c.enc₂ z.1.2 i), z.2 i))
      (fun t => t.1.1) Prod.snd (fun t => t.1.2)
    rw [c.dist_jointLaw_letter hW i] at e1
    rw [macInfo₁, ← e1, condMutualInfo_comm hμ, condMutualInfo]
    rfl
  have hfano := hH ▸ (show H[W₁ | W₂ ; μ] = I[W₁ : Y | W₂ ; μ] + H[W₁ | pair Y W₂ ; μ] by
    rw [condMutualInfo]; ring)
  rw [c.condEntropy_out_msg hW] at hI
  have hsum : ∑ i, macInfo₁ (c.letterDist₁ i) (c.letterDist₂ i) W =
      ∑ i, H[fun z => z.2 i | fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => c.enc₂ z.1.2 i ; μ] -
        ∑ i, H[fun z => z.2 i | fun z => (c.enc₁ z.1.1 i, c.enc₂ z.1.2 i) ; μ] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => (hterm i).symm
  linarith

/-- **(15.115)** `log M₂ ≤ ∑ᵢ I(X₂ᵢ; Yᵢ | X₁ᵢ) + log 2 + Pₑ^(n) log (M₁ M₂)`. -/
theorem log_le_macInfo₂ :
    log M₂ ≤ ∑ i, macInfo₂ (c.letterDist₁ i) (c.letterDist₂ i) W + log 2 +
      c.avgErrProb W * log (M₁ * M₂) := by
  set μ := c.jointLaw W
  have hμ : IsPMF μ := c.jointLaw_isPMF hW h₁ h₂
  set Wv : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₁ × Fin M₂ := Prod.fst
  set W₁ : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₁ := fun z => z.1.1
  set W₂ : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₂ := fun z => z.1.2
  set Y : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin n → β := Prod.snd
  have hH : H[W₂ | W₁ ; μ] = log M₂ := by
    rw [condEntropy_eq_sub hμ]
    have e : H[pair W₁ W₂ ; μ] = H[Wv ; μ] := rfl
    rw [e, c.entropy_msg hW h₁ h₂, c.entropy_msg₁ hW h₁ h₂,
      log_mul (by positivity) (by positivity)]
    ring
  have hF : H[W₂ | pair Y W₁ ; μ] ≤ log 2 + c.avgErrProb W * log (M₁ * M₂) := by
    have e : H[W₂ | pair Y W₁ ; μ] = H[W₂ | pair W₁ Y ; μ] :=
      condEntropy_congr_right hμ W₂ Prod.swap Prod.swap_injective fun _ => rfl
    have h1 := condEntropy_le_condEntropy hμ W₂ W₁ Y
    have h2 := condEntropy_comp_le hμ Wv Y Prod.snd
    have h3 := c.condEntropy_msg_le hW h₁ h₂
    rw [e]
    exact h1.trans (h2.trans h3)
  have hI : I[W₂ : Y | W₁ ; μ] = H[Y | W₁ ; μ] - H[Y | Wv ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
    congr 1
    exact condEntropy_congr_right hμ Y Prod.swap Prod.swap_injective fun _ => rfl
  have hY : H[Y | W₁ ; μ] ≤ ∑ i, H[fun z => z.2 i |
      fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => c.enc₁ z.1.1 i ; μ] :=
    (condEntropy_pi_le_sum hμ Y W₁).trans (sum_le_sum fun i _ =>
      condEntropy_le_condEntropy_comp hμ _ W₁ (fun w => c.enc₁ w i))
  have hterm : ∀ i, H[fun z => z.2 i | fun z : (Fin M₁ × Fin M₂) × (Fin n → β) =>
      c.enc₁ z.1.1 i ; μ] - H[fun z => z.2 i | fun z => (c.enc₁ z.1.1 i, c.enc₂ z.1.2 i) ; μ] =
      macInfo₂ (c.letterDist₁ i) (c.letterDist₂ i) W := by
    intro i
    have e1 := condMutualInfo_comp hμ
      (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => ((c.enc₁ z.1.1 i, c.enc₂ z.1.2 i), z.2 i))
      (fun t => t.1.2) Prod.snd (fun t => t.1.1)
    rw [c.dist_jointLaw_letter hW i] at e1
    rw [macInfo₂, ← e1, condMutualInfo_comm hμ, condMutualInfo]
    congr 1
    exact (condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl).symm
  have hfano := hH ▸ (show H[W₂ | W₁ ; μ] = I[W₂ : Y | W₁ ; μ] + H[W₂ | pair Y W₁ ; μ] by
    rw [condMutualInfo]; ring)
  rw [c.condEntropy_out_msg hW] at hI
  have hsum : ∑ i, macInfo₂ (c.letterDist₁ i) (c.letterDist₂ i) W =
      ∑ i, H[fun z => z.2 i | fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => c.enc₁ z.1.1 i ; μ] -
        ∑ i, H[fun z => z.2 i | fun z => (c.enc₁ z.1.1 i, c.enc₂ z.1.2 i) ; μ] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => (hterm i).symm
  linarith

/-- **(15.116)–(15.125)** `log (M₁ M₂) ≤ ∑ᵢ I(X₁ᵢ, X₂ᵢ; Yᵢ) + log 2 + Pₑ^(n) log (M₁ M₂)`. -/
theorem log_mul_le_macInfo₁₂ :
    log (M₁ * M₂) ≤ ∑ i, macInfo₁₂ (c.letterDist₁ i) (c.letterDist₂ i) W + log 2 +
      c.avgErrProb W * log (M₁ * M₂) := by
  set μ := c.jointLaw W
  have hμ : IsPMF μ := c.jointLaw_isPMF hW h₁ h₂
  set Wv : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin M₁ × Fin M₂ := Prod.fst
  set Y : (Fin M₁ × Fin M₂) × (Fin n → β) → Fin n → β := Prod.snd
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ Wv Y
  have h2 := mutualInfo_eq_entropy_sub_condEntropy' hμ Wv Y
  have h3 := c.condEntropy_msg_le hW h₁ h₂
  have h4 := c.entropy_msg hW h₁ h₂
  have hY : H[Y ; μ] ≤ ∑ i, H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.2 i ; μ] := by
    have := condEntropy_pi_le_sum hμ Y (fun _ => ())
    simp only [condEntropy_const hμ] at this
    exact this
  have hterm : ∀ i, H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.2 i ; μ] -
      H[fun z => z.2 i | fun z => (c.enc₁ z.1.1 i, c.enc₂ z.1.2 i) ; μ] =
      macInfo₁₂ (c.letterDist₁ i) (c.letterDist₂ i) W := by
    intro i
    have e1 := mutualInfo_comp (μ := μ)
      (fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => ((c.enc₁ z.1.1 i, c.enc₂ z.1.2 i), z.2 i))
      Prod.fst Prod.snd
    rw [c.dist_jointLaw_letter hW i] at e1
    rw [macInfo₁₂, ← e1, mutualInfo_eq_entropy_sub_condEntropy' hμ]
    rfl
  rw [c.condEntropy_out_msg hW] at h2
  have hsum : ∑ i, macInfo₁₂ (c.letterDist₁ i) (c.letterDist₂ i) W =
      ∑ i, H[fun z : (Fin M₁ × Fin M₂) × (Fin n → β) => z.2 i ; μ] -
        ∑ i, H[fun z => z.2 i | fun z => (c.enc₁ z.1.1 i, c.enc₂ z.1.2 i) ; μ] := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ => (hterm i).symm
  linarith

end Bounds

end MACCode

/-! ### The converse -/

lemma le_log_ceil_exp (x : ℝ) : x ≤ log ⌈exp x⌉₊ := by
  calc x = log (exp x) := (log_exp x).symm
    _ ≤ log ⌈exp x⌉₊ := log_le_log (exp_pos x) (Nat.le_ceil _)

lemma log_ceil_exp_le (x : ℝ) : log ⌈exp x⌉₊ ≤ |x| + log 2 := by
  have h1 : (⌈exp x⌉₊ : ℝ) ≤ 2 * exp |x| := by
    have := Nat.ceil_lt_add_one (exp_pos x).le
    have h2 : exp x ≤ exp |x| := exp_le_exp.2 (le_abs_self x)
    have h3 : 1 ≤ exp |x| := one_le_exp (abs_nonneg x)
    linarith
  have hpos : (0 : ℝ) < ⌈exp x⌉₊ := by exact_mod_cast one_le_ceil_exp x
  calc log ⌈exp x⌉₊ ≤ log (2 * exp |x|) := log_le_log hpos h1
    _ = |x| + log 2 := by rw [log_mul two_ne_zero (exp_pos _).ne', log_exp]; ring

variable {W : α₁ × α₂ → β → ℝ}

/-- **Theorems 15.3.1 and 15.3.4 (converse), (15.96)–(15.131).** Every achievable rate pair is in
the closure of the region `R₁ ≤ I(X₁; Y | X₂, Q)`, `R₂ ≤ I(X₂; Y | X₁, Q)`,
`R₁ + R₂ ≤ I(X₁, X₂; Y | Q)`: for the codes of block length `n`, `Q` is uniform on the `n`
columns of the codebooks, and the rates exceed the bounds by at most
`εₙ = (log 2 + Pₑ^(n) log (M₁ M₂))/n → 0`. -/
theorem IsAchievableMAC.mem_closure_macRegion (hW : IsChannel W) {R₁ R₂ : ℝ}
    (h : IsAchievableMAC W R₁ R₂) : (R₁, R₂) ∈ closure (macRegion W) := by
  obtain ⟨c, hc⟩ := h
  set M₁ : ℕ → ℕ := fun n => ⌈exp (n * R₁)⌉₊
  set M₂ : ℕ → ℕ := fun n => ⌈exp (n * R₂)⌉₊
  set P : ℕ → ℝ := fun n => (c n).avgErrProb W
  set ε : ℕ → ℝ := fun n => (log 2 + P n * log (M₁ n * M₂ n)) / n
  have hM₁ : ∀ n, 0 < M₁ n := fun n => one_le_ceil_exp _
  have hM₂ : ∀ n, 0 < M₂ n := fun n => one_le_ceil_exp _
  have hlog : ∀ n, 0 ≤ log ((M₁ n : ℝ) * M₂ n) := fun n => by
    have h1 : (1 : ℝ) ≤ M₁ n := by exact_mod_cast hM₁ n
    have h2 : (1 : ℝ) ≤ M₂ n := by exact_mod_cast hM₂ n
    exact log_nonneg (by nlinarith)
  have hε0 : ∀ n, 0 ≤ ε n := fun n => div_nonneg (add_nonneg (log_pos one_lt_two).le
    (mul_nonneg ((c n).avgErrProb_nonneg hW) (hlog n))) (Nat.cast_nonneg n)
  -- The rate pairs `(R₁ - εₙ, R₂ - εₙ)` are in the region, with `Q` uniform on `{0, …, n - 1}`.
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ macRegion W := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have b₁ : log (M₁ n) ≤ ∑ i, macInfo₁ ((c n).letterDist₁ i) ((c n).letterDist₂ i) W +
        log 2 + P n * log (M₁ n * M₂ n) := (c n).log_le_macInfo₁ hW (hM₁ n) (hM₂ n)
    have b₂ : log (M₂ n) ≤ ∑ i, macInfo₂ ((c n).letterDist₁ i) ((c n).letterDist₂ i) W +
        log 2 + P n * log (M₁ n * M₂ n) := (c n).log_le_macInfo₂ hW (hM₁ n) (hM₂ n)
    have b₃ : log (M₁ n * M₂ n) ≤
        ∑ i, macInfo₁₂ ((c n).letterDist₁ i) ((c n).letterDist₂ i) W +
        log 2 + P n * log (M₁ n * M₂ n) := (c n).log_mul_le_macInfo₁₂ hW (hM₁ n) (hM₂ n)
    have l₁ : n * R₁ ≤ log (M₁ n) := le_log_ceil_exp _
    have l₂ : n * R₂ ≤ log (M₂ n) := le_log_ceil_exp _
    have l₁₂ : log ((M₁ n : ℝ) * M₂ n) = log (M₁ n) + log (M₂ n) :=
      log_mul (by exact_mod_cast (hM₁ n).ne') (by exact_mod_cast (hM₂ n).ne')
    have hq : IsPMF (fun _ : Fin n => (1 : ℝ) / n) :=
      ⟨fun _ => by positivity, by simp [hn'.ne']⟩
    have key : ∀ (a S : ℝ), n * a ≤ S + (log 2 + P n * log (M₁ n * M₂ n)) →
        a - ε n ≤ S / n := fun a S h => by
      simp only [ε]
      rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hn']
      linarith
    refine ⟨n, fun _ => 1 / n, fun i => (c n).letterDist₁ i, fun i => (c n).letterDist₂ i, hq,
      fun i => (c n).letterDist₁_isPMF (hM₁ n) i, fun i => (c n).letterDist₂_isPMF (hM₂ n) i,
      ?_, ?_, ?_⟩
    · rw [← mul_sum, one_div_mul_eq_div]
      exact key _ _ (by linarith)
    · rw [← mul_sum, one_div_mul_eq_div]
      exact key _ _ (by linarith)
    · rw [← mul_sum, one_div_mul_eq_div]
      have := key (R₁ + R₂) (∑ i, macInfo₁₂ ((c n).letterDist₁ i) ((c n).letterDist₂ i) W)
        (by linarith)
      linarith [hε0 n]
  -- `εₙ → 0`.
  have hε : Tendsto ε atTop (𝓝 0) := by
    set K := |R₁| + |R₂| + 2
    have hP0 : Tendsto P atTop (𝓝 0) := hc
    have hup : Tendsto (fun n : ℕ => log 2 / n + P n * K) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (log 2)).add (hP0.mul_const K)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall hε0) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hl₁ := log_ceil_exp_le (n * R₁)
    have hl₂ := log_ceil_exp_le (n * R₂)
    rw [abs_mul, Nat.abs_cast] at hl₁ hl₂
    have hl : log ((M₁ n : ℝ) * M₂ n) ≤ n * K := by
      rw [log_mul (by exact_mod_cast (hM₁ n).ne') (by exact_mod_cast (hM₂ n).ne')]
      have : log 2 < 1 := by
        have := log_two_lt_d9
        linarith
      simp only [M₁, M₂, K]
      nlinarith
    simp only [ε]
    rw [add_div, mul_div_assoc]
    gcongr
    · exact (c n).avgErrProb_nonneg hW
    · rw [div_le_iff₀ hn']
      linarith
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

end InfoTheory
