/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BinarySymmetricBC
public import InfoTheoryLib.Network.RelayOrth

/-!
# The modulo-2 sum relay channel

The example of pages 17-51 and 17-52 of the notes, due to Aleksic, Razaghi and Yu: `Y' = X ⊕ Z` and
`Y₁ = Z ⊕ Z₁`, for `Z ∼ Bern(1/2)`, `Z₁ ∼ Bern(p)` and `X` independent, and a channel `p(y'' | x₁)`
from the relay to the receiver with capacity `C₀`. Its capacity is `1 - H(p ∗ H⁻¹(1 - C₀))`, which
is smaller than the cutset bound.

## Main definitions

* `msP p`: the channel from `X` to `(Y', Y₁)`.

## Main statements

* `isAchievableRC_modSum`: the capacity is achieved by compress–forward.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- **Page 17-51 of [elgamal2010].** The channel from `X` to `(Y', Y₁)`, with `Z = X ⊕ Y'`. -/
def msP (p : ℝ) (x : Bool) (o : Bool × Bool) : ℝ := 2⁻¹ * bsbcBSC p (xor x o.1) o.2

lemma msP_isChannel {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsChannel (msP p) := fun x => by
  have hB := bsbcBSC_isChannel h0 h1
  refine ⟨fun o => mul_nonneg (by norm_num) ((hB _).nonneg _), ?_⟩
  simp only [msP, Fintype.sum_prod_type, ← mul_sum, (hB _).sum_eq_one]
  simp

/-- The law of `(X, Z)`. -/
def msξ₁ : Bool × Bool → ℝ := fun _ => 4⁻¹

lemma msξ₁_isPMF : IsPMF msξ₁ := ⟨fun _ => by simp [msξ₁], by simp [msξ₁]⟩

/-- The law of a Bernoulli variable. -/
def msBern (p : ℝ) : Bool → ℝ := fun b => if b then p else 1 - p

lemma msBern_isPMF {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsPMF (msBern p) := by
  refine ⟨fun b => ?_, by simp [msBern]⟩
  cases b <;> simp [msBern, h0, h1]

/-- The law of `(Z₁, W)`, for the noise `W` of the description. -/
def msξ₂ (p α : ℝ) : Bool × Bool → ℝ := prodDist (msBern p) (msBern α)

/-- The variables of the part `(X, (Y', Y₁), Ŷ₁)`, as functions of the independent variables. -/
def msΦ (t : (Bool × Bool) × (Bool × Bool)) : (Bool × (Bool × Bool)) × Bool :=
  ((t.1.1, (xor t.1.1 t.1.2, xor t.1.2 t.2.1)), xor (xor t.1.2 t.2.1) t.2.2)

/-- The inverse of `msΦ`. -/
def msΨ (o : (Bool × (Bool × Bool)) × Bool) : (Bool × Bool) × (Bool × Bool) :=
  ((o.1.1, xor o.1.1 o.1.2.1), (xor (xor o.1.1 o.1.2.1) o.1.2.2, xor o.1.2.2 o.2))

lemma msΦ_msΨ (o : (Bool × (Bool × Bool)) × Bool) : msΦ (msΨ o) = o := by
  obtain ⟨⟨x, y, s⟩, v⟩ := o
  cases x <;> cases y <;> cases s <;> cases v <;> rfl

lemma msΨ_msΦ (t : (Bool × Bool) × (Bool × Bool)) : msΨ (msΦ t) = t := by
  obtain ⟨⟨x, z⟩, a, w⟩ := t
  cases x <;> cases z <;> cases a <;> cases w <;> rfl

/-- The part of the law of compress–forward with `X` uniform and `Ŷ₁ = Y₁ ⊕ W`. -/
lemma dist_msΦ (p α : ℝ) :
    dist (prodDist msξ₁ (msξ₂ p α)) msΦ = roν₁ (uniformPMF Bool) (msP p) (bsbcBSC α) := by
  classical
  funext o
  simp only [dist]
  rw [sum_eq_single (msΨ o)]
  · simp only [msΦ_msΨ, ite_true]
    obtain ⟨⟨x, y, s⟩, v⟩ := o
    cases x <;> cases y <;> cases s <;> cases v <;>
      simp [prodDist, msξ₁, msξ₂, msBern, roν₁, jointOf, msP, bsbcBSC, uniformPMF, msΨ] <;> ring
  · intro t _ ht
    have : msΦ t ≠ o := fun h => ht (by rw [← h, msΨ_msΦ])
    exact ite_eq_right this
  · simp

section Entropies

variable {p α : ℝ}

lemma msξ₂_isPMF (hp : 0 ≤ p) (hp' : p ≤ 1) (hα : 0 ≤ α) (hα' : α ≤ 1) : IsPMF (msξ₂ p α) :=
  (msBern_isPMF hp hp').prodDist (msBern_isPMF hα hα')

lemma entropy_msBern (hp : 0 ≤ p) (hp' : p ≤ 1) : entropy (msBern p) = binEntropy p := by
  rw [entropy_bool (msBern_isPMF hp hp')]
  simp [msBern]

lemma entropy_msξ₁ : entropy msξ₁ = 2 * log 2 := by
  have h : msξ₁ = uniformPMF (Bool × Bool) := by
    funext t
    simp [msξ₁, uniformPMF]
  rw [h, entropy_uniformPMF]
  simp only [Fintype.card_prod, Fintype.card_bool]
  have : ((2 * 2 : ℕ) : ℝ) = 2 ^ 2 := by norm_num
  rw [this, log_pow]
  norm_num

lemma entropy_msξ₁_fst : H[Prod.fst ; msξ₁] = log 2 := by
  have h : dist msξ₁ Prod.fst = uniformPMF Bool := by
    funext a
    rw [dist_fst]
    simp [msξ₁, uniformPMF]
    norm_num
  rw [entropyRV, h, entropy_uniformPMF]
  simp

lemma entropy_msξ₁_xor : H[fun t : Bool × Bool => xor t.1 t.2 ; msξ₁] = log 2 := by
  have h : dist msξ₁ (fun t : Bool × Bool => xor t.1 t.2) = uniformPMF Bool := by
    funext a
    cases a <;> simp [dist, msξ₁, uniformPMF, Fintype.sum_prod_type] <;> norm_num
  rw [entropyRV, h, entropy_uniformPMF]
  simp

lemma entropy_msξ₂_fst (hp : 0 ≤ p) (hp' : p ≤ 1) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    H[Prod.fst ; msξ₂ p α] = binEntropy p := by
  rw [entropyRV, msξ₂, dist_prodDist_fst (msBern_isPMF hα hα'), entropy_msBern hp hp']

lemma entropy_msξ₂_id (hp : 0 ≤ p) (hp' : p ≤ 1) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    entropy (msξ₂ p α) = binEntropy p + binEntropy α := by
  rw [msξ₂, entropy_prodDist (msBern_isPMF hp hp') (msBern_isPMF hα hα'), entropy_msBern hp hp',
    entropy_msBern hα hα']

lemma entropy_msξ₂_xor (hp : 0 ≤ p) (hp' : p ≤ 1) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    H[fun t : Bool × Bool => xor t.1 t.2 ; msξ₂ p α] = binEntropy (binConv α p) := by
  have hξ := msξ₂_isPMF hp hp' hα hα'
  rw [entropyRV, entropy_bool (hξ.dist _)]
  congr 1
  simp only [dist, Fintype.sum_prod_type, Fintype.sum_bool, msξ₂, prodDist, msBern, binConv]
  simp
  ring

/-- An entropy of the part `(X, (Y', Y₁), Ŷ₁)`, as the sum of the entropies of the independent
variables. -/
lemma entropy_ms {C D E : Type*} [Fintype C] [Fintype D] [Fintype E] (hξ : IsPMF (msξ₂ p α))
    (g : Bool × Bool → C) (h : Bool × Bool → D) (f : (Bool × (Bool × Bool)) × Bool → E)
    (j : C × D → E) (hj : Function.Injective j) (hf : ∀ t, f (msΦ t) = j (g t.1, h t.2)) :
    H[f ; roν₁ (uniformPMF Bool) (msP p) (bsbcBSC α)] = H[g ; msξ₁] + H[h ; msξ₂ p α] := by
  rw [← dist_msΦ, ← entropy_prod_parts msξ₁_isPMF hξ g h]
  have e : H[f ; dist (prodDist msξ₁ (msξ₂ p α)) msΦ] = H[f ∘ msΦ ; prodDist msξ₁ (msξ₂ p α)] :=
    entropyRV_dist _ _ _
  rw [e]
  exact entropyRV_eq_of_injective _ j hj hf

/-- `I(X; Y') = 0`. -/
lemma ms_info₁ (hp : 0 ≤ p) (hp' : p ≤ 1) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    I[fun z => z.1.1 : fun z => z.1.2.1 ; roν₁ (uniformPMF Bool) (msP p) (bsbcBSC α)] = 0 := by
  have hξ := msξ₂_isPMF hp hp' hα hα'
  have hν := roν₁_isPMF (uniformPMF_isPMF (α := Bool)) (msP_isChannel hp hp')
    (bsbcBSC_isChannel hα hα')
  rw [mutualInfo_eq_add_sub hν]
  have h₀ : H[fun _ : Bool × Bool => () ; msξ₂ p α] = 0 := entropyRV_const hξ ()
  have h₁ := entropy_ms hξ Prod.fst (fun _ => ()) (fun z => z.1.1) Prod.fst
    (fun a b h => Prod.ext h rfl) fun _ => rfl
  have h₂ := entropy_ms hξ (fun t : Bool × Bool => xor t.1 t.2) (fun _ => ()) (fun z => z.1.2.1)
    Prod.fst (fun a b h => Prod.ext h rfl) fun _ => rfl
  have h₃ := entropy_ms hξ id (fun _ => ())
    (pair (fun z => z.1.1) fun z => z.1.2.1) (fun t => (t.1.1, xor t.1.1 t.1.2))
    (by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all) fun _ => rfl
  have e : H[id ; msξ₁] = entropy msξ₁ := by simp only [entropyRV, dist_id]
  rw [h₁, h₂, h₃, h₀, e, entropy_msξ₁, entropy_msξ₁_fst, entropy_msξ₁_xor]
  ring

/-- `I(Y₁; Ŷ₁ | X, Y') = H(α ∗ p) - H(α)`. -/
lemma ms_info₂ (hp : 0 ≤ p) (hp' : p ≤ 1) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    I[fun z => z.1.2.2 : fun z => z.2 | fun z => (z.1.1, z.1.2.1) ;
      roν₁ (uniformPMF Bool) (msP p) (bsbcBSC α)] = binEntropy (binConv α p) - binEntropy α := by
  have hξ := msξ₂_isPMF hp hp' hα hα'
  have hν := roν₁_isPMF (uniformPMF_isPMF (α := Bool)) (msP_isChannel hp hp')
    (bsbcBSC_isChannel hα hα')
  rw [condMutualInfo_eq_entropies hν]
  have h₀ : H[fun _ : Bool × Bool => () ; msξ₂ p α] = 0 := entropyRV_const hξ ()
  have h₁ := entropy_ms hξ id (fun _ => ())
    (fun z => (z.1.1, z.1.2.1)) (fun t => (t.1.1, xor t.1.1 t.1.2))
    (by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      cases a <;> cases b <;> cases a' <;> cases b' <;> simp_all) fun _ => rfl
  have h₂ := entropy_ms hξ id Prod.fst
    (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.1.2.2)
    (fun t => ((t.1.1, xor t.1.1 t.1.2), xor t.1.2 t.2))
    (by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> simp_all)
    fun _ => rfl
  have h₃ := entropy_ms hξ id (fun t : Bool × Bool => xor t.1 t.2)
    (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2)
    (fun t => ((t.1.1, xor t.1.1 t.1.2), xor t.1.2 t.2))
    (by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> simp_all)
    (by
      rintro ⟨⟨a, b⟩, c, d⟩
      cases a <;> cases b <;> cases c <;> cases d <;> rfl)
  have h₄ := entropy_ms hξ id id
    (pair (pair (fun z => (z.1.1, z.1.2.1)) fun z => z.2) fun z => z.1.2.2)
    (fun t => (((t.1.1, xor t.1.1 t.1.2), xor (xor t.1.2 t.2.1) t.2.2), xor t.1.2 t.2.1))
    (by
      rintro ⟨⟨a, b⟩, c, d⟩ ⟨⟨a', b'⟩, c', d'⟩ h
      cases a <;> cases b <;> cases c <;> cases d <;> cases a' <;> cases b' <;> cases c' <;>
        cases d' <;> simp_all)
    fun _ => rfl
  have e : H[id ; msξ₁] = entropy msξ₁ := by simp only [entropyRV, dist_id]
  have e₂ : H[id ; msξ₂ p α] = entropy (msξ₂ p α) := by simp only [entropyRV, dist_id]
  rw [h₁, h₂, h₃, h₄, h₀, e, e₂, entropy_msξ₁, entropy_msξ₂_fst hp hp' hα hα',
    entropy_msξ₂_id hp hp' hα hα', entropy_msξ₂_xor hp hp' hα hα']
  ring

/-- `I(X; Y', Ŷ₁) = log 2 - H(α ∗ p)`. -/
lemma ms_info₃ (hp : 0 ≤ p) (hp' : p ≤ 1) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    I[fun z => z.1.1 : fun z => (z.1.2.1, z.2) ; roν₁ (uniformPMF Bool) (msP p) (bsbcBSC α)] =
      log 2 - binEntropy (binConv α p) := by
  have hξ := msξ₂_isPMF hp hp' hα hα'
  have hν := roν₁_isPMF (uniformPMF_isPMF (α := Bool)) (msP_isChannel hp hp')
    (bsbcBSC_isChannel hα hα')
  rw [mutualInfo_eq_add_sub hν]
  have h₀ : H[fun _ : Bool × Bool => () ; msξ₂ p α] = 0 := entropyRV_const hξ ()
  have h₁ := entropy_ms hξ Prod.fst (fun _ => ()) (fun z => z.1.1) Prod.fst
    (fun a b h => Prod.ext h rfl) fun _ => rfl
  have h₃ := entropy_ms hξ id (fun t : Bool × Bool => xor t.1 t.2)
    (pair (fun z => z.1.1) fun z => (z.1.2.1, z.2))
    (fun t => (t.1.1, (xor t.1.1 t.1.2, xor t.1.2 t.2)))
    (by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;> simp_all)
    (by
      rintro ⟨⟨a, b⟩, c, d⟩
      cases a <;> cases b <;> cases c <;> cases d <;> rfl)
  -- `(Y', Ŷ₁)` is uniform
  have h₄ : H[fun z => (z.1.2.1, z.2) ; roν₁ (uniformPMF Bool) (msP p) (bsbcBSC α)] = 2 *
    log 2 := by
    have hd : dist (roν₁ (uniformPMF Bool) (msP p) (bsbcBSC α)) (fun z => (z.1.2.1, z.2)) =
      msξ₁ := by
      rw [← dist_msΦ, ← dist_comp_eq]
      funext ⟨a, b⟩
      cases a <;> cases b <;>
        simp [dist, Fintype.sum_prod_type, prodDist, msξ₁, msξ₂, msBern, msΦ] <;>
        ring
    rw [entropyRV, hd, entropy_msξ₁]
  have e : H[id ; msξ₁] = entropy msξ₁ := by simp only [entropyRV, dist_id]
  rw [h₁, h₃, h₄, h₀, e, entropy_msξ₁, entropy_msξ₁_fst, entropy_msξ₂_xor hp hp' hα hα']
  ring

end Entropies

/-! ### Achievability -/

section Achievability

variable {U Y'' : Type*} [Fintype U] [Fintype Y''] [Nonempty U] [Nonempty Y''] {κ : U → Y'' → ℝ}
  {p : ℝ}

/-- **The capacity of the modulo-2 sum relay channel**, in nats:
`log 2 - H(H⁻¹(log 2 - C₀) ∗ p)`. -/
def msCap (p C₀ : ℝ) : ℝ := log 2 - mrsGerber p (log 2 - C₀)

/-- **Page 17-52 of [elgamal2010].** Every rate below `1 - H(p ∗ H⁻¹(1 - C₀))` is achievable, by
compress–forward with `Ŷ₁ = Y₁ ⊕ V`, for `V ∼ Bern(H⁻¹(1 - C₀))`. -/
theorem isAchievableRC_modSum (hp : 0 ≤ p) (hp' : p ≤ 1) (hκ : IsChannel κ)
    (hC : capacity κ ≤ log 2) {R : ℝ} (hR : R * log 2 < msCap p (capacity κ)) :
    IsAchievableRC (rcRO (msP p) κ) R := by
  obtain ⟨p₁, hp₁, hcap⟩ := exists_capacity_eq hκ
  have hC0 : 0 ≤ capacity κ := hcap ▸ mutualInfoOf_nonneg hp₁ hκ
  have hv : log 2 - capacity κ ∈ Set.Icc 0 (log 2) := ⟨by linarith, by linarith⟩
  set α := binEntropyInv (log 2 - capacity κ) with hαd
  have hα := binEntropyInv_mem hv
  have hα0 : 0 ≤ α := hα.1
  have hα1 : α ≤ 1 := hα.2.trans (by norm_num)
  have hent : binEntropy α = log 2 - capacity κ := binEntropy_binEntropyInv hv
  have hR' : R * log 2 < log 2 - binEntropy (binConv α p) := hR
  refine isAchievableRC_ro (V := Bool) (τ' := bsbcBSC α) uniformPMF_isPMF hp₁ (msP_isChannel hp hp')
    hκ (bsbcBSC_isChannel hα0 hα1) ?_ ?_
  · rw [ms_info₁ hp hp' hα0 hα1, ms_info₂ hp hp' hα0 hα1, hcap, hent]
    linarith
  · rw [ms_info₃ hp hp' hα0 hα1]
    exact hR'

end Achievability

/-! ### The converse -/

section Converse

variable {U Y'' : Type*} [Fintype U] [Fintype Y''] {κ : U → Y'' → ℝ} {p : ℝ} {M n : ℕ}
  (c : RCCode M n Bool U (Bool × Y'') Bool)

/-- The prefix of a sequence of the relay. -/
def msPre (y₁ : Fin n → Bool) (k : ℕ) : Fin k → Bool :=
  fun i => if h : (i : ℕ) < n then y₁ ⟨i, h⟩ else false

/-- The relay, as an encoder whose message is the whole sequence that it receives. -/
def msEnc : ∀ k, (Fin n → Bool) → (Fin k → Y'') → U := fun k y₁ _ => c.relay k (msPre y₁ k)

/-- The law of `(Y₁ⁿ, Y''ⁿ)`: `Y₁ⁿ` is uniform, and `Y''ⁿ` is the output of the channel from the
relay to the receiver. -/
def msΓ (κ : U → Y'' → ℝ) : (Fin n → Bool) × (Fin n → Y'') → ℝ :=
  fbLaw (uniformPMF _) κ (msEnc c) n

/-- The law of `(Z₁ⁿ, Y₁ⁿ, Y''ⁿ)`. -/
def msΘ (p : ℝ) (κ : U → Y'' → ℝ) : (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')) → ℝ :=
  prodDist (iidPMF (msBern p) n) (msΓ c κ)

/-- The law of `(M, Z₁ⁿ, Y₁ⁿ, Y''ⁿ)`. -/
def msΛ (p : ℝ) (κ : U → Y'' → ℝ) :
    Fin M × ((Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y''))) → ℝ :=
  prodDist (uniformPMF (Fin M)) (msΘ c p κ)

/-- The sequence `Zⁿ = Y₁ⁿ ⊕ Z₁ⁿ`. -/
def msZ (t : (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y''))) : Fin n → Bool :=
  fun i => xor (t.2.1 i) (t.1 i)

/-- The map from `(M, Z₁ⁿ, Y₁ⁿ, Y''ⁿ)` to the message and the outputs of the channel. -/
def msMap (t : Fin M × ((Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')))) :
    Fin M × (Fin n → (Bool × Y'') × Bool) :=
  (t.1, fun i => ((xor (c.enc i t.1) (msZ t.2 i), t.2.2.2 i), t.2.2.1 i))

/-- The inverse of `msMap`. -/
def msInv (o : Fin M × (Fin n → (Bool × Y'') × Bool)) :
    Fin M × ((Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y''))) :=
  (o.1, (fun i => xor (xor (c.enc i o.1) (o.2 i).1.1) (o.2 i).2,
    (fun i => (o.2 i).2, fun i => (o.2 i).1.2)))

omit [Fintype U] [Fintype Y''] in
lemma msMap_msInv (o : Fin M × (Fin n → (Bool × Y'') × Bool)) : msMap c (msInv c o) = o := by
  refine Prod.ext rfl (funext fun i => ?_)
  simp only [msMap, msInv, msZ]
  refine Prod.ext (Prod.ext ?_ rfl) rfl
  dsimp only
  cases c.enc i o.1 <;> cases (o.2 i).1.1 <;> cases (o.2 i).2 <;> rfl

omit [Fintype U] [Fintype Y''] in
lemma msInv_msMap (t : Fin M × ((Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')))) :
    msInv c (msMap c t) = t := by
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
  simp only [msMap, msInv, msZ]
  cases c.enc i t.1 <;> cases t.2.1 i <;> cases t.2.2.1 i <;> rfl

omit [Fintype U] in
/-- **The law of the code**, in terms of the noise. -/
lemma dist_msMap :
    dist (msΛ c p κ) (msMap c) = c.law (rcRO (msP p) κ) n := by
  classical
  funext o
  simp only [dist]
  rw [sum_eq_single (msInv c o)]
  · simp only [msMap_msInv, ite_true]
    obtain ⟨w, z⟩ := o
    rw [RCCode.law, fbLaw_eq_prod]
    simp only [msΛ, msΘ, msΓ, prodDist, msInv]
    rw [fbLaw_eq_prod]
    congr 1
    have hun : uniformPMF (Fin n → Bool) (fun i => (z i).2) = ∏ _i : Fin n, (2⁻¹ : ℝ) := by
      simp [uniformPMF]
    rw [hun, iidPMF, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    have hpre : msPre (fun j => (z j).2) (i : ℕ) = fun t : Fin i => (z ⟨t, t.2.trans i.2⟩).2 := by
      funext t
      simp [msPre, t.2.trans i.2]
    simp only [msEnc, hpre, RCCode.fbEnc, rcRO, msP, msBern]
    have hb : ∀ a b d : Bool, (if (xor (xor a b) d) = true then p else 1 - p) =
        bsbcBSC p (xor a b) d := by
      intro a b d
      cases a <;> cases b <;> cases d <;> simp [bsbcBSC]
    rw [hb]
    ring
  · intro t _ ht
    have : msMap c t ≠ o := fun h => ht (by rw [← h, msInv_msMap])
    exact ite_eq_right this
  · simp

section Info

variable [Nonempty U]

omit [Nonempty U] in
lemma msBern_dist_coord (hp : 0 ≤ p) (hp' : p ≤ 1) (i : Fin n) :
    dist (iidPMF (msBern p) n) (fun ω => ω i) = msBern p :=
  dist_iidPMF_apply (msBern_isPMF hp hp') i

omit [Fintype U] [Nonempty U] in
lemma msΓ_isPMF (hκ : IsChannel κ) : IsPMF (msΓ c κ) :=
  fbLaw_isPMF uniformPMF_isPMF hκ n

omit [Fintype U] [Nonempty U] in
lemma msΘ_isPMF (hp : 0 ≤ p) (hp' : p ≤ 1) (hκ : IsChannel κ) : IsPMF (msΘ c p κ) :=
  (iidPMF_isPMF (msBern_isPMF hp hp') n).prodDist (msΓ_isPMF c hκ)

omit [Nonempty U] in
/-- **The bound from Mrs. Gerber's lemma**, pages 17-52 of [elgamal2010]: for `C₀` the capacity of
the channel, `H(H⁻¹(1 - C₀) ∗ p) ≤ H(Zⁿ | Y''ⁿ) / n`. -/
theorem ms_gerber (hp : 0 ≤ p) (hp' : p ≤ 1) (hκ : IsChannel κ) (hC : capacity κ ≤ log 2)
    (hC0 : 0 ≤ capacity κ) (hn : 0 < n) :
    mrsGerber p (log 2 - capacity κ) ≤
      H[msZ | fun t => t.2.2 ; msΘ c p κ] / n := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hΘ := msΘ_isPMF c hp hp' hκ
  have hΓ := msΓ_isPMF c hκ
  have hν : IsPMF (iidPMF (msBern p) n) := iidPMF_isPMF (msBern_isPMF hp hp') n
  -- the variables
  let Xv : ℕ → (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')) → Bool :=
    fun i ω => if h : i < n then ω.2.1 ⟨i, h⟩ else false
  let Zv : ℕ → (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')) → Bool :=
    fun i ω => if h : i < n then ω.1 ⟨i, h⟩ else false
  have hXp : prefixRV Xv n = fun ω => ω.2.1 := by
    funext ω i
    simp [prefixRV, Xv]
  have hZp : prefixRV Zv n = Prod.fst := by
    funext ω i
    simp [prefixRV, Zv]
  have hxp : prefixRV (fun i ω => xor (Xv i ω) (Zv i ω)) n = msZ := by
    funext ω i
    simp [prefixRV, Xv, Zv, msZ]
  have hfst : dist (msΘ c p κ) Prod.fst = iidPMF (msBern p) n :=
    dist_prodDist_fst hΓ _
  have hcoord : ∀ i : Fin n, dist (msΘ c p κ) (Zv i) = msBern p := by
    intro i
    have e : Zv i = (fun ω : Fin n → Bool => ω i) ∘ Prod.fst := by
      funext ω
      simp [Zv]
    rw [e, dist_comp_eq, hfst, msBern_dist_coord hp hp']
  have hZ : ∀ i < n, dist (msΘ c p κ) (Zv i) true = p := by
    intro i hi
    have := hcoord ⟨i, hi⟩
    simp only at this
    rw [this]
    simp [msBern]
  have hfam : IndepFamily (msΘ c p κ) Zv n := by
    intro v
    rw [hZp, hfst]
    simp only [iidPMF]
    refine prod_congr rfl fun i _ => ?_
    rw [hcoord i]
  have hind : IndepRV (msΘ c p κ) (prefixRV Zv n)
      (pair (prefixRV Xv n) fun t => t.2.2) := by
    intro v w
    have hs : (pair (prefixRV Xv n) fun t : (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')) =>
        t.2.2) = Prod.snd := by
      rw [hXp]
      rfl
    have hsnd : dist (msΘ c p κ) Prod.snd = msΓ c κ := dist_prodDist_snd hν _
    rw [hs, hZp, hfst, hsnd]
    have hpair : pair (Prod.fst : (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')) → _) Prod.snd =
        id := rfl
    rw [hpair, dist_id]
    rfl
  have hm := mrsGerber_le_condEntropy_xor_prefixRV hΘ Xv Zv (fun t => t.2.2) hn hZ hfam hind
  rw [hxp] at hm
  refine le_trans ?_ hm
  -- the entropy of `Y₁ⁿ` given `Y''ⁿ`
  have hv := condEntropy_prefixRV_div_mem_Icc hΘ Xv (fun t => t.2.2) hn
  refine mrsGerber_monotoneOn ⟨hp, hp'⟩ ⟨by linarith, by linarith⟩ hv ?_
  rw [hXp, le_div_iff₀ hn']
  have hd : dist (msΘ c p κ) (pair (fun t => t.2.2) fun t => t.2.1) =
      dist (msΓ c κ) (pair Prod.snd Prod.fst) := by
    have e : (pair (fun t => t.2.2) fun t => t.2.1 :
        (Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y'')) → _) =
        (pair Prod.snd Prod.fst) ∘ Prod.snd := rfl
    have hsnd : dist (msΘ c p κ) Prod.snd = msΓ c κ := dist_prodDist_snd hν _
    rw [e, dist_comp_eq, hsnd]
  have hce := condEntropy_eq_of_dist_pair_eq hΘ hΓ hd
  rw [hce]
  have hI := mutualInfo_eq_entropy_sub_condEntropy hΓ
    (Prod.fst : (Fin n → Bool) × (Fin n → Y'') → _) Prod.snd
  have hle : I[Prod.fst : Prod.snd ; msΓ c κ] ≤ n * capacity κ :=
    mutualInfo_fbLaw_le uniformPMF_isPMF hκ n
  have hH : H[Prod.fst ; msΓ c κ] = n * log 2 := by
    have hd : dist (msΓ c κ) Prod.fst = uniformPMF (Fin n → Bool) := dist_fst_fbLaw hκ n
    rw [entropyRV, hd, entropy_uniformPMF]
    simp
  linarith

omit [Fintype U] [Nonempty U] in
/-- **The converse, page 17-52 of [elgamal2010]**: `I(M; Yⁿ) ≤ n (log 2 - H(Zⁿ | Y''ⁿ) / n)`. -/
theorem ms_info_le (hM : 0 < M) (hp : 0 ≤ p) (hp' : p ≤ 1) (hκ : IsChannel κ) :
    I[Prod.fst : rcY ; c.law (rcRO (msP p) κ) n] ≤
      n * log 2 - H[msZ | fun t => t.2.2 ; msΘ c p κ] := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hUn : IsPMF (uniformPMF (Fin M)) := uniformPMF_isPMF
  have hΘ := msΘ_isPMF c hp hp' hκ
  have hΛ : IsPMF (msΛ c p κ) := hUn.prodDist hΘ
  have hlaw := c.law_isPMF hM (rcRO_isChannel (msP_isChannel hp hp') hκ) n
  rw [mutualInfo_eq_add_sub hlaw, ← dist_msMap]
  simp only [entropyRV_dist]
  -- the message
  have h₁ : H[Prod.fst ∘ msMap c ; msΛ c p κ] = entropy (uniformPMF (Fin M)) := by
    have e : (Prod.fst ∘ msMap c : _ → Fin M) = Prod.fst := rfl
    rw [e, entropyRV, msΛ, dist_prodDist_fst hΘ]
  -- the message and the outputs
  have h₂ : H[pair Prod.fst rcY ∘ msMap c ; msΛ c p κ] = entropy (uniformPMF (Fin M)) +
      H[fun t => (msZ t, t.2.2) ; msΘ c p κ] := by
    have h := entropy_prod_parts hUn hΘ (id : Fin M → Fin M) (fun t => (msZ t, t.2.2))
    have e : H[id ; uniformPMF (Fin M)] = entropy (uniformPMF (Fin M)) := by
      simp only [entropyRV, dist_id]
    rw [e] at h
    rw [← h]
    refine entropyRV_eq_of_injective _
      (fun t : Fin M × ((Fin n → Bool) × (Fin n → Y'')) =>
        ((t.1, fun i => (xor (c.enc i t.1) (t.2.1 i), t.2.2 i)) :
          Fin M × (Fin n → Bool × Y''))) ?_ fun _ => rfl
    rintro ⟨m, z, y⟩ ⟨m', z', y'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h₂⟩ := h
    have hz : z = z' := funext fun i => by
      have := (Prod.ext_iff.mp (congrFun h₂ i)).1
      simpa using this
    have hy : y = y' := funext fun i => (Prod.ext_iff.mp (congrFun h₂ i)).2
    rw [hz, hy]
  -- the outputs
  have h₃ : H[rcY ∘ msMap c ; msΛ c p κ] ≤ n * log 2 + H[fun t => t.2.2 ; msΘ c p κ] := by
    set Ya : Fin M × ((Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y''))) → (Fin n → Bool) :=
      fun t i => xor (c.enc i t.1) (msZ t.2 i) with hYa
    set Yb : Fin M × ((Fin n → Bool) × ((Fin n → Bool) × (Fin n → Y''))) → (Fin n → Y'') :=
      fun t => t.2.2.2 with hYb
    have e₁ : H[rcY ∘ msMap c ; msΛ c p κ] = H[pair Ya Yb ; msΛ c p κ] := by
      refine entropyRV_eq_of_injective _
        (fun t : (Fin n → Bool) × (Fin n → Y'') => ((fun i => (t.1 i, t.2 i)) : Fin n → Bool × Y''))
        ?_ fun _ => rfl
      rintro ⟨a, b⟩ ⟨a', b'⟩ h
      exact Prod.ext (funext fun i => (Prod.ext_iff.mp (congrFun h i)).1)
        (funext fun i => (Prod.ext_iff.mp (congrFun h i)).2)
    have hnn := mutualInfo_nonneg hΛ Ya Yb
    rw [mutualInfo_eq_add_sub hΛ] at hnn
    have e₂ : H[Ya ; msΛ c p κ] ≤ n * log 2 := by
      have := entropyRV_le_log_card hΛ Ya
      simpa using this
    have e₃ : H[Yb ; msΛ c p κ] = H[fun t => t.2.2 ; msΘ c p κ] := by
      have e : Yb = (fun t => t.2.2) ∘ Prod.snd := rfl
      rw [e, entropyRV, dist_comp_eq, msΛ, dist_prodDist_snd hUn]
      rfl
    rw [e₁]
    linarith
  -- the chain rule
  have h₄ : H[fun t => (msZ t, t.2.2) ; msΘ c p κ] = H[fun t => t.2.2 ; msΘ c p κ] +
      H[msZ | fun t => t.2.2 ; msΘ c p κ] := by
    rw [← chain_rule hΘ]
    exact entropyRV_eq_of_injective _ (fun t : (Fin n → Y'') × (Fin n → Bool) => (t.2, t.1))
      (fun a b h => Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)) fun _ => rfl
  rw [h₁, h₂, h₄]
  linarith

end Info

end Converse

/-! ### The capacity -/

section Capacity

variable {U Y'' : Type*} [Fintype U] [Fintype Y''] [Nonempty U] [Nonempty Y''] {κ : U → Y'' → ℝ}
  {p : ℝ}

/-- **Pages 17-51 and 17-52 of [elgamal2010].** The capacity of the modulo-2 sum relay channel is
`1 - H(p ∗ H⁻¹(1 - C₀))` bits, where `C₀` is the capacity of the channel from the relay to the
receiver, in nats here. -/
theorem rcCapacity_modSum (hp : 0 ≤ p) (hp' : p ≤ 1) (hκ : IsChannel κ)
    (hC : capacity κ ≤ log 2) :
    rcCapacity (rcRO (msP p) κ) = msCap p (capacity κ) / log 2 := by
  obtain ⟨p₁, hp₁, hcap⟩ := exists_capacity_eq hκ
  have hC0 : 0 ≤ capacity κ := hcap ▸ mutualInfoOf_nonneg hp₁ hκ
  refine rcCapacity_eq (fun R hR => isAchievableRC_modSum hp hp' hκ hC hR) fun R hR => ?_
  refine hR.le_of_info_bound (rcRO_isChannel (msP_isChannel hp hp') hκ) fun n hn c => ?_
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (ms_info_le c (by positivity) hp hp' hκ).trans ?_
  have h := ms_gerber c hp hp' hκ hC hC0 hn
  rw [le_div_iff₀ hn'] at h
  simp only [msCap]
  nlinarith

/-- `I(X; Y', Y₁) = log 2 - H(p)` for `X` uniform. -/
lemma ms_info_bc (hp : 0 ≤ p) (hp' : p ≤ 1) :
    mutualInfoOf (uniformPMF Bool) (msP p) = log 2 - binEntropy p := by
  have hchan := msP_isChannel hp hp'
  have hν : IsPMF (roν₁ (uniformPMF Bool) (msP p) (bsbcBSC 0)) :=
    roν₁_isPMF uniformPMF_isPMF hchan (bsbcBSC_isChannel le_rfl zero_le_one)
  have h₃ := ms_info₃ (α := 0) hp hp' le_rfl zero_le_one
  have hb : binConv 0 p = p := by simp [binConv]
  rw [hb] at h₃
  rw [← h₃]
  -- `Ŷ₁ = Y₁`
  have hle : mutualInfoOf (uniformPMF Bool) (msP p) =
      I[fun z => z.1.1 : fun z => z.1.2 ; roν₁ (uniformPMF Bool) (msP p) (bsbcBSC 0)] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    have hfst : dist (roν₁ (uniformPMF Bool) (msP p) (bsbcBSC 0)) Prod.fst =
        jointOf (uniformPMF Bool) (msP p) := dist_jointOf_fst fun _ => bsbcBSC_isChannel le_rfl
          zero_le_one _
    have e : (pair (fun z : (Bool × (Bool × Bool)) × Bool => z.1.1) fun z => z.1.2) =
        (pair Prod.fst Prod.snd) ∘ Prod.fst := rfl
    rw [e, dist_comp_eq, hfst]
  rw [hle]
  refine mutualInfo_eq_of_dist_pair_eq ?_
  funext ⟨x, y, v⟩
  simp [dist, pair, Fintype.sum_prod_type, roν₁, jointOf, bsbcBSC]
  cases v <;> cases x <;> cases y <;> simp

omit [Nonempty Y''] in
/-- **Page 17-52 of [elgamal2010]: the cutset bound is not tight.** For `0 < p < 1/2` and
`0 < C₀ < log 2`, the capacity of the modulo-2 sum relay channel is strictly smaller than the cutset
bound. -/
theorem modSum_lt_cutset (hp : 0 < p) (hp' : p < 2⁻¹) (hκ : IsChannel κ) (hC0 : 0 < capacity κ)
    (hC : capacity κ < log 2) : msCap p (capacity κ) < rcCutsetBound (rcRO (msP p) κ) := by
  obtain ⟨p₁, hp₁, hcap⟩ := exists_capacity_eq hκ
  have hp1 : p ≤ 1 := by linarith [hp'.le, (by norm_num : (2 : ℝ)⁻¹ ≤ 1)]
  have hW := rcRO_isChannel (msP_isChannel hp.le hp1) hκ
  have hv : log 2 - capacity κ ∈ Set.Icc 0 (log 2) := ⟨by linarith, by linarith⟩
  set α := binEntropyInv (log 2 - capacity κ) with hαd
  have hα : α ∈ Set.Icc 0 2⁻¹ := binEntropyInv_mem hv
  have hent : binEntropy α = log 2 - capacity κ := binEntropy_binEntropyInv hv
  have hα0 : 0 < α := by
    rcases hα.1.lt_or_eq with h | h
    · exact h
    · rw [← h, binEntropy_zero] at hent
      linarith
  have hα1 : α < 2⁻¹ := by
    rcases hα.2.lt_or_eq with h | h
    · exact h
    · rw [h, binEntropy_two_inv] at hent
      linarith
  have hconv : binConv α p ∈ Set.Icc 0 2⁻¹ := binConv_mem_Icc_half hα ⟨hp.le, hp'.le⟩
  have hgt₁ : p < binConv α p := by
    rw [binConv_eq]
    have : 0 < (1 - 2 * p) * α := mul_pos (by linarith) hα0
    linarith
  have hgt₂ : α < binConv α p := by
    rw [binConv, show α * (1 - p) + (1 - α) * p = α + p * (1 - 2 * α) by ring]
    have : 0 < p * (1 - 2 * α) := mul_pos hp (by linarith)
    linarith
  have hm := binEntropy_strictMonoOn
  have h₁ : binEntropy p < binEntropy (binConv α p) :=
    hm ⟨hp.le, hp'.le⟩ hconv hgt₁
  have h₂ : binEntropy α < binEntropy (binConv α p) :=
    hm ⟨hα.1, hα.2⟩ hconv hgt₂
  have hcapv : msCap p (capacity κ) = log 2 - binEntropy (binConv α p) := rfl
  -- the value of the cutset bound for independent inputs
  have hval : min (log 2 - binEntropy p) (capacity κ) ≤ rcCutsetBound (rcRO (msP p) κ) := by
    refine le_trans ?_ (le_csSup (bddAbove_rcCutset hW)
      ⟨prodDist (uniformPMF Bool) p₁, (uniformPMF_isPMF).prodDist hp₁, rfl⟩)
    rw [rcMacInfo_ro_prod uniformPMF_isPMF hp₁ (msP_isChannel hp.le hp1) hκ,
      rcBcInfo_ro_prod uniformPMF_isPMF hp₁ (msP_isChannel hp.le hp1) hκ, ms_info_bc hp.le hp1,
        hcap]
    have := mutualInfo_nonneg (jointOf_isPMF (uniformPMF_isPMF (α := Bool))
      (msP_isChannel hp.le hp1)) Prod.fst (fun z : Bool × (Bool × Bool) => z.2.1)
    exact le_min ((min_le_right _ _).trans (by linarith)) (min_le_left _ _)
  refine lt_of_lt_of_le ?_ hval
  rw [hcapv]
  refine lt_min (by linarith) (by linarith)

end Capacity

end InfoTheory
