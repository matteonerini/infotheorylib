/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.BCBits
public import InfoTheoryLib.Network.MACConverse

/-!
# Laws for the degraded broadcast channel

The single-letter facts behind the converse of Theorem 2 of Lecture 5 of El Gamal and Kim: the
information quantities of the law `p(u, x) p(y₁, y₂ | x)`, and a time-sharing variable absorbed into
the auxiliary random variable.

## Main definitions

* `degradedBCTimeShare w q`: the law of `((Q, U), X)` for a time-sharing variable `Q` with law `w`.
* `degradedBCRelabelLaw`: the law `p(u, x)` with the auxiliary variable relabelled.

## Main statements

* `bcInfoXY₁U_degradedBCTimeShare`, `sum_mul_bcInfoUY₂_le_degradedBCTimeShare`: time sharing.
* `degradedBC_bcInfoUY₂_le_bcInfoUY₁_of_physicallyDegraded`: `I(U; Y₂) ≤ I(U; Y₁)` for a physically
  degraded channel.
* `degradedBC_bcInfoXY₁U_relabel`, `degradedBC_bcInfoUY₂_relabel`: relabelling the auxiliary
  variable does not change the information quantities.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 5
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section General

variable {Ω τ γ δ β : Type*} [Fintype Ω] [Fintype τ] [Fintype γ] [Fintype δ] [Fintype β]
  {μ : Ω → ℝ}

omit [Fintype τ] [Fintype γ] [Fintype δ] [Fintype β] in
/-- If `Y` is produced from `T` by the channel `K ∘ ρ`, it is produced by `K ∘ f` from any
coarsening `G(T)` that still determines `ρ(T) = f(G(T))`. -/
lemma dist_pair_comp_of_channel [Finite τ] [Finite β] {ι : Type*} {T : Ω → τ} {Y : Ω → β}
    {ρ : τ → ι}
    {K : ι → β → ℝ} (h : ∀ t y, dist μ (pair T Y) (t, y) = dist μ T t * K (ρ t) y)
    (G : τ → γ) (f : γ → ι) (hf : ∀ t, f (G t) = ρ t) (c : γ) (y : β) :
    dist μ (pair (G ∘ T) Y) (c, y) = dist μ (G ∘ T) c * K (f c) y := by
  classical
  have := Fintype.ofFinite τ
  have := Fintype.ofFinite β
  have e1 : pair (G ∘ T) Y = Prod.map G id ∘ pair T Y := rfl
  rw [e1, dist_comp, dist_comp, Fintype.sum_prod_type, sum_mul]
  refine sum_congr rfl fun t _ => ?_
  rw [sum_eq_single y (fun b _ hb => by simp [hb]) (by simp)]
  by_cases ht : G t = c
  · simp [ht, h, ← hf t]
  · simp [ht]

/-- If `X' = f(X)` and `X = g(X')`, then `H(X' | A) = H(X | A)`. -/
lemma degradedBC_condEntropy_eq_of_comp_eq (hμ : IsPMF μ) {X : Ω → γ} {X' : Ω → δ} (A : Ω → τ)
    (f : γ → δ) (g : δ → γ) (hf : ∀ ω, X' ω = f (X ω)) (hg : ∀ ω, X ω = g (X' ω)) :
    H[X' | A ; μ] = H[X | A ; μ] := by
  have h1 := condEntropy_comp_le hμ X A f
  have h2 := condEntropy_comp_le hμ X' A g
  rw [show f ∘ X = X' from funext fun ω => (hf ω).symm] at h1
  rw [show g ∘ X' = X from funext fun ω => (hg ω).symm] at h2
  linarith

omit [Fintype γ] in
/-- The law of `(Q, F_Q)` under the mixture `w(i) μᵢ(ω)` of laws. -/
private lemma dist_mixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (μ : ι → Ω → ℝ)
    (F : ι → Ω → γ) (i : ι) (a : γ) :
    dist (fun z : ι × Ω => w z.1 * μ z.1 z.2) (fun z => (z.1, F z.1 z.2)) (i, a) =
      w i * dist (μ i) (F i) a := by
  classical
  simp only [dist, Fintype.sum_prod_type, Prod.mk.injEq, mul_sum]
  rw [sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp_all

/-- **Time sharing.** Conditioning on the time-sharing variable `Q`: under the mixture
`w(i) μᵢ(ω)`, `H(Y_Q | Q, C_Q) = ∑ᵢ w(i) H(Yᵢ | Cᵢ)`. -/
lemma condEntropy_mixture {ι : Type*} [Fintype ι] (w : ι → ℝ) (μ : ι → Ω → ℝ)
    (Y : ι → Ω → β) (C : ι → Ω → γ) :
    H[fun z : ι × Ω => Y z.1 z.2 | fun z => (z.1, C z.1 z.2) ;
      fun z : ι × Ω => w z.1 * μ z.1 z.2] = ∑ i, w i * H[Y i | C i ; μ i] := by
  set ν := fun z : ι × Ω => w z.1 * μ z.1 z.2
  have hC := dist_mixture w μ C
  have hCY : ∀ i c y, dist ν (pair (fun z : ι × Ω => (z.1, C z.1 z.2))
      (fun z => Y z.1 z.2)) ((i, c), y) = w i * dist (μ i) (pair (C i) (Y i)) (c, y) := by
    intro i c y
    have := dist_eq_of_injective ν (U := fun z : ι × Ω => (z.1, pair (C z.1) (Y z.1) z.2))
      (V := pair (fun z : ι × Ω => (z.1, C z.1 z.2)) (fun z => Y z.1 z.2))
      (fun t : ι × γ × β => ((t.1, t.2.1), t.2.2))
      (fun a b hab => by
        obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
        simp only [Prod.mk.injEq] at hab ⊢; tauto) (fun _ => rfl) (i, c, y)
    rw [this]
    exact dist_mixture w μ (fun i => pair (C i) (Y i)) i (c, y)
  unfold condEntropy
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [hC, mul_assoc]
  by_cases hw : w i = 0
  · simp [hw]
  · congr 2
    unfold condEntropyAt
    congr 1
    funext y
    rw [condDist, condDist, hCY, hC, mul_div_mul_left _ _ hw]

end General

/-! ### The single-letter law `p(u, x) p(y₁, y₂ | x)` -/

section SingleLetter

variable {α β₁ β₂ 𝒰 : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] [Fintype 𝒰]
  {q : 𝒰 × α → ℝ} {W : α → β₁ × β₂ → ℝ}

private lemma dist_bcJoint_fst_fst (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) (t : 𝒰 × α)
    (y₁ : β₁) : dist (bcJoint q W) (fun z => (z.1, z.2.1)) (t, y₁) = q t * bcMarg₁ W t.2 y₁ := by
  classical
  rw [dist, Fintype.sum_prod_type, sum_eq_single t
    (fun t' _ ht' => sum_eq_zero fun y _ => by simp [ht']) (by simp), Fintype.sum_prod_type,
    sum_eq_single y₁ (fun b _ hb => sum_eq_zero fun y₂ _ => by simp [hb]) (by simp)]
  simp [bcJoint, jointOf, bcMarg₁, mul_sum]

private lemma dist_bcJoint_fst_snd (q : 𝒰 × α → ℝ) (W : α → β₁ × β₂ → ℝ) (t : 𝒰 × α)
    (y₂ : β₂) : dist (bcJoint q W) (fun z => (z.1, z.2.2)) (t, y₂) = q t * bcMarg₂ W t.2 y₂ := by
  classical
  rw [dist, Fintype.sum_prod_type, sum_eq_single t
    (fun t' _ ht' => sum_eq_zero fun y _ => by simp [ht']) (by simp), Fintype.sum_prod_type,
    sum_comm, sum_eq_single y₂ (fun b _ hb => sum_eq_zero fun y₁ _ => by simp [hb]) (by simp)]
  simp [bcJoint, jointOf, bcMarg₂, mul_sum]

private lemma dist_bcJoint_fst (hW : IsChannel W) (t : 𝒰 × α) :
    dist (bcJoint q W) Prod.fst t = q t := by
  rw [dist_fst]
  simp only [bcJoint, jointOf, ← mul_sum, (hW _).sum_eq_one, mul_one]

/-- In a physically degraded channel `p(y₁ | x) p(y₂ | y₁)`, given `(U, X, Y₁)` the output `Y₂` is
produced from `Y₁` by `p(y₂ | y₁)`. -/
private lemma dist_bcJoint_degraded {W₁ : α → β₁ → ℝ} {V : β₁ → β₂ → ℝ} (hV : IsChannel V)
    (hd : ∀ x y₁ y₂, W x (y₁, y₂) = W₁ x y₁ * V y₁ y₂) (s : (𝒰 × α) × β₁) (y₂ : β₂) :
    dist (bcJoint q W) (pair (fun z => (z.1, z.2.1)) (fun z => z.2.2)) (s, y₂) =
      dist (bcJoint q W) (fun z => (z.1, z.2.1)) s * V s.2 y₂ := by
  obtain ⟨t, y₁⟩ := s
  have hinj : Function.Injective
      (pair (fun z : (𝒰 × α) × (β₁ × β₂) => (z.1, z.2.1)) (fun z => z.2.2)) := fun a b h => by
    obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
    simp only [pair, Prod.mk.injEq] at h ⊢; tauto
  have e1 : dist (bcJoint q W) (pair (fun z : (𝒰 × α) × (β₁ × β₂) => (z.1, z.2.1))
      (fun z => z.2.2)) ((t, y₁), y₂) = bcJoint q W (t, (y₁, y₂)) := by
    have := dist_comp_of_injective (bcJoint q W) id hinj (t, (y₁, y₂))
    rwa [dist_id] at this
  rw [e1, dist_bcJoint_fst_fst]
  simp only [bcJoint, jointOf, bcMarg₁, hd, ← mul_sum, (hV y₁).sum_eq_one, mul_one]
  ring

/-- `Y₁` is produced from `X` by `p(y₁ | x)`, whatever the conditioning on `U`. -/
private lemma dist_bcJoint_out₁ (hW : IsChannel W) (t : 𝒰 × α) (y₁ : β₁) :
    dist (bcJoint q W) (pair Prod.fst (fun z => z.2.1)) (t, y₁) =
      dist (bcJoint q W) Prod.fst t * bcMarg₁ W t.2 y₁ := by
  rw [dist_bcJoint_fst hW]
  exact dist_bcJoint_fst_fst q W t y₁

/-- In a physically degraded channel, `I(X; Y₁, Y₂ | U) = I(X; Y₁ | U)`. -/
lemma degradedBC_condMutualInfo_out_eq (hq : IsPMF q) (hW : IsChannel W)
    (hd : IsPhysicallyDegraded W) :
    I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2 : Prod.snd | fun z => z.1.1 ; bcJoint q W] =
      bcInfoXY₁U q W := by
  obtain ⟨W₁, V, -, hV, hdW⟩ := hd
  have hμ : IsPMF (bcJoint q W) := bcJoint_isPMF hq hW
  have hch := dist_bcJoint_degraded (q := q) hV hdW
  have hA : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 | pair (fun z => z.2.1) (fun z => z.1.1) ;
      bcJoint q W] =
      ∑ y, dist (bcJoint q W) (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) y * entropy (V y) :=
    condEntropy_of_channel Prod.fst
      (dist_pair_comp_of_channel hch (fun s => (s.2, s.1.1)) Prod.fst (fun _ => rfl))
  have hB : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 |
      pair (fun z => z.2.1) (pair (fun z => z.1.2) (fun z => z.1.1)) ; bcJoint q W] =
      ∑ y, dist (bcJoint q W) (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) y * entropy (V y) :=
    condEntropy_of_channel Prod.fst
      (dist_pair_comp_of_channel hch (fun s => (s.2, (s.1.2, s.1.1))) Prod.fst (fun _ => rfl))
  have h1 := chain_rule_cond hμ (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) (fun z => z.2.2)
    (fun z => z.1.1)
  have h2 := chain_rule_cond hμ (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) (fun z => z.2.2)
    (pair (fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2) (fun z => z.1.1))
  rw [condMutualInfo_comm hμ, bcInfoXY₁U,
    condMutualInfo_comm hμ (fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2) (fun z => z.2.1)]
  unfold condMutualInfo
  change H[pair (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) (fun z => z.2.2) | fun z => z.1.1 ;
      bcJoint q W] - H[pair (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) (fun z => z.2.2) |
      pair (fun z => z.1.2) (fun z => z.1.1) ; bcJoint q W] = _
  linarith

/-- **Lecture 5 of [elgamal2010].** Since `U → X → Y₁`, `I(X; Y₁) = I(U; Y₁) + I(X; Y₁ | U)`. -/
theorem bcInfoXY₁_eq_bcInfoUY₁_add_bcInfoXY₁U (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₁ q W = bcInfoUY₁ q W + bcInfoXY₁U q W := by
  have hμ : IsPMF (bcJoint q W) := bcJoint_isPMF hq hW
  have hch := dist_bcJoint_out₁ (q := q) hW
  have hA : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1 | fun z => z.1.2 ; bcJoint q W] =
      ∑ x, dist (bcJoint q W) (fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2) x * entropy (bcMarg₁ W x) :=
    condEntropy_of_channel id (dist_pair_comp_of_channel hch Prod.snd id (fun _ => rfl))
  have hB : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1 | pair (fun z => z.1.2) (fun z => z.1.1) ;
      bcJoint q W] =
      ∑ x, dist (bcJoint q W) (fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2) x * entropy (bcMarg₁ W x) :=
    condEntropy_of_channel Prod.fst
      (dist_pair_comp_of_channel hch (fun t => (t.2, t.1)) Prod.fst (fun _ => rfl))
  rw [bcInfoXY₁, bcInfoUY₁, bcInfoXY₁U, condMutualInfo_comm hμ, condMutualInfo,
    mutualInfo_eq_entropy_sub_condEntropy' hμ, mutualInfo_eq_entropy_sub_condEntropy' hμ]
  linarith

/-- `I(X; Y₁ | U)` only depends on `p(u, x)` and `p(y₁ | x)`. -/
lemma degradedBC_bcInfoXY₁U_eq_jointOf (hq : IsPMF q) (hW : IsChannel W) :
    bcInfoXY₁U q W = I[fun t : (𝒰 × α) × β₁ => t.1.2 : Prod.snd | fun t => t.1.1 ;
      jointOf q fun t => bcMarg₁ W t.2] := by
  have hd : dist (bcJoint q W) (fun z => (z.1, z.2.1)) = jointOf q fun t => bcMarg₁ W t.2 :=
    funext fun s => dist_bcJoint_fst_fst q W s.1 s.2
  have e := condMutualInfo_comp (bcJoint_isPMF hq hW) (fun z => (z.1, z.2.1))
    (fun t : (𝒰 × α) × β₁ => t.1.2) Prod.snd (fun t => t.1.1)
  rw [hd] at e
  exact e

/-- `I(U; Y₁)` only depends on `p(u, x)` and `p(y₁ | x)`. -/
lemma degradedBC_bcInfoUY₁_eq_jointOf :
    bcInfoUY₁ q W = I[fun t : (𝒰 × α) × β₁ => t.1.1 : Prod.snd ;
      jointOf q fun t => bcMarg₁ W t.2] := by
  have hd : dist (bcJoint q W) (fun z => (z.1, z.2.1)) = jointOf q fun t => bcMarg₁ W t.2 :=
    funext fun s => dist_bcJoint_fst_fst q W s.1 s.2
  have e := mutualInfo_comp (μ := bcJoint q W) (fun z => (z.1, z.2.1))
    (fun t : (𝒰 × α) × β₁ => t.1.1) Prod.snd
  rw [hd] at e
  exact e

/-- `I(U; Y₂)` only depends on `p(u, x)` and `p(y₂ | x)`. -/
lemma degradedBC_bcInfoUY₂_eq_jointOf :
    bcInfoUY₂ q W = I[fun t : (𝒰 × α) × β₂ => t.1.1 : Prod.snd ;
      jointOf q fun t => bcMarg₂ W t.2] := by
  have hd : dist (bcJoint q W) (fun z => (z.1, z.2.2)) = jointOf q fun t => bcMarg₂ W t.2 :=
    funext fun s => dist_bcJoint_fst_snd q W s.1 s.2
  have e := mutualInfo_comp (μ := bcJoint q W) (fun z => (z.1, z.2.2))
    (fun t : (𝒰 × α) × β₂ => t.1.1) Prod.snd
  rw [hd] at e
  exact e

/-- Data processing for a physically degraded channel: `U → Y₁ → Y₂`, so `I(U; Y₂) ≤ I(U; Y₁)`. -/
lemma degradedBC_bcInfoUY₂_le_bcInfoUY₁_of_physicallyDegraded (hq : IsPMF q) (hW : IsChannel W)
    (hd : IsPhysicallyDegraded W) : bcInfoUY₂ q W ≤ bcInfoUY₁ q W := by
  obtain ⟨W₁, V, -, hV, hdW⟩ := hd
  have hμ : IsPMF (bcJoint q W) := bcJoint_isPMF hq hW
  have hch := dist_bcJoint_degraded (q := q) hV hdW
  have hA : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 | fun z => z.2.1 ; bcJoint q W] =
      ∑ y, dist (bcJoint q W) (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) y * entropy (V y) :=
    condEntropy_of_channel id (dist_pair_comp_of_channel hch Prod.snd id (fun _ => rfl))
  have hB : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 | pair (fun z => z.1.1) (fun z => z.2.1) ;
      bcJoint q W] =
      ∑ y, dist (bcJoint q W) (fun z : (𝒰 × α) × (β₁ × β₂) => z.2.1) y * entropy (V y) :=
    condEntropy_of_channel Prod.snd
      (dist_pair_comp_of_channel hch (fun s => (s.1.1, s.2)) Prod.snd (fun _ => rfl))
  have h0 : I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1 : fun z => z.2.2 | fun z => z.2.1 ;
      bcJoint q W] = 0 := by
    rw [condMutualInfo_comm hμ, condMutualInfo]
    linarith
  have h1 := chain_rule_mutualInfo₂ hμ (fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1) (fun z => z.2.2)
    (fun z => z.2.1)
  have h2 := chain_rule_mutualInfo₂ hμ (fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1) (fun z => z.2.1)
    (fun z => z.2.2)
  have h3 : I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1 : pair (fun z => z.2.2) (fun z => z.2.1) ;
      bcJoint q W] = I[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1 :
        pair (fun z => z.2.1) (fun z => z.2.2) ; bcJoint q W] :=
    mutualInfo_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have h4 := condMutualInfo_nonneg hμ (fun z : (𝒰 × α) × (β₁ × β₂) => z.1.1) (fun z => z.2.1)
    (fun z => z.2.2)
  rw [bcInfoUY₂, bcInfoUY₁]
  linarith

end SingleLetter

/-! ### Time sharing and relabelling the auxiliary variable -/

section TimeSharing

variable {α β₁ β₂ 𝒰 𝒰' ι : Type*} [Fintype α] [Fintype β₁] [Fintype β₂] [Fintype 𝒰] [Fintype 𝒰']
  [Fintype ι] {W : α → β₁ × β₂ → ℝ}

/-- The law `w(i) qᵢ(u, x)` of `((Q, U), X)`: the time-sharing variable `Q` has law `w`, and given
`Q = i`, the pair `(U, X)` has law `qᵢ`. -/
def degradedBCTimeShare (w : ι → ℝ) (q : ι → 𝒰 × α → ℝ) : (ι × 𝒰) × α → ℝ :=
  fun z => w z.1.1 * q z.1.1 (z.1.2, z.2)

lemma degradedBCTimeShare_isPMF {w : ι → ℝ} (hw : IsPMF w) {q : ι → 𝒰 × α → ℝ}
    (hq : ∀ i, IsPMF (q i)) : IsPMF (degradedBCTimeShare w q) := by
  refine ⟨fun z => mul_nonneg (hw.nonneg _) ((hq _).nonneg _), ?_⟩
  have h : ∀ i, ∑ u, ∑ x, q i (u, x) = 1 := fun i => by
    rw [← Fintype.sum_prod_type']
    exact (hq i).sum_eq_one
  simp only [degradedBCTimeShare, Fintype.sum_prod_type, ← mul_sum, h, mul_one]
  exact hw.sum_eq_one

/-- Reassociating `(((i, u), x), y)` as `(i, ((u, x), y))`. -/
private def timeShareEquiv (ι 𝒰 α γ : Type*) : ((ι × 𝒰) × α) × γ ≃ ι × ((𝒰 × α) × γ) where
  toFun z := (z.1.1.1, ((z.1.1.2, z.1.2), z.2))
  invFun t := (((t.1, t.2.1.1), t.2.1.2), t.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private lemma dist_bcJoint_timeShare (w : ι → ℝ) (q : ι → 𝒰 × α → ℝ) :
    dist (bcJoint (degradedBCTimeShare w q) W) (timeShareEquiv ι 𝒰 α (β₁ × β₂)) =
      fun z => w z.1 * bcJoint (q z.1) W z.2 := by
  have h := dist_comp_equiv (fun z : ι × ((𝒰 × α) × (β₁ × β₂)) => w z.1 * bcJoint (q z.1) W z.2)
    (timeShareEquiv ι 𝒰 α (β₁ × β₂))
  rw [← h]
  congr 1
  funext z
  simp only [bcJoint, jointOf, degradedBCTimeShare, timeShareEquiv, Equiv.coe_fn_mk]
  ring

/-- **Time sharing.** `I(X; Y₁ | Q, U) = ∑ᵢ w(i) I(X; Y₁ | U, Q = i)`. -/
theorem bcInfoXY₁U_degradedBCTimeShare {w : ι → ℝ} (hw : IsPMF w) {q : ι → 𝒰 × α → ℝ}
    (hq : ∀ i, IsPMF (q i)) (hW : IsChannel W) :
    bcInfoXY₁U (degradedBCTimeShare w q) W = ∑ i, w i * bcInfoXY₁U (q i) W := by
  have hμ := bcJoint_isPMF (degradedBCTimeShare_isPMF hw hq) hW
  have hν := hμ.dist (timeShareEquiv ι 𝒰 α (β₁ × β₂))
  have e := condMutualInfo_comp hμ (timeShareEquiv ι 𝒰 α (β₁ × β₂))
    (fun t => t.2.1.2) (fun t => t.2.2.1) (fun t => (t.1, t.2.1.1))
  rw [dist_bcJoint_timeShare] at e hν
  refine e.trans ?_
  have h1 := condEntropy_mixture w (fun i => bcJoint (q i) W)
    (fun _ (z : (𝒰 × α) × (β₁ × β₂)) => z.1.2) (fun _ z => z.1.1)
  have h2 := condEntropy_mixture w (fun i => bcJoint (q i) W)
    (fun _ (z : (𝒰 × α) × (β₁ × β₂)) => z.1.2) (fun _ z => (z.2.1, z.1.1))
  have h3 := condEntropy_congr_right hν (fun t : ι × ((𝒰 × α) × (β₁ × β₂)) => t.2.1.2)
    (X := fun t => (t.1, (t.2.2.1, t.2.1.1)))
    (X' := pair (fun t => t.2.2.1) (fun t => (t.1, t.2.1.1)))
    (fun s : ι × β₁ × 𝒰 => (s.2.1, (s.1, s.2.2)))
    (fun a b hab => by
      obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b
      simp only [Prod.mk.injEq] at hab ⊢; tauto) (fun _ => rfl)
  rw [condMutualInfo, h3]
  refine (congrArg₂ _ h1 h2).trans ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [bcInfoXY₁U, condMutualInfo, mul_sub]
  rfl

/-- **Time sharing.** `∑ᵢ w(i) I(U; Y₂ | Q = i) ≤ I(Q, U; Y₂)`. -/
theorem sum_mul_bcInfoUY₂_le_degradedBCTimeShare {w : ι → ℝ} (hw : IsPMF w) {q : ι → 𝒰 × α → ℝ}
    (hq : ∀ i, IsPMF (q i)) (hW : IsChannel W) :
    ∑ i, w i * bcInfoUY₂ (q i) W ≤ bcInfoUY₂ (degradedBCTimeShare w q) W := by
  have hμ := bcJoint_isPMF (degradedBCTimeShare_isPMF hw hq) hW
  have hν := hμ.dist (timeShareEquiv ι 𝒰 α (β₁ × β₂))
  have e := mutualInfo_comp (μ := bcJoint (degradedBCTimeShare w q) W)
    (timeShareEquiv ι 𝒰 α (β₁ × β₂)) (fun t => (t.1, t.2.1.1)) (fun t => t.2.2.2)
  rw [dist_bcJoint_timeShare] at e hν
  have h0 : bcInfoUY₂ (degradedBCTimeShare w q) W = _ := e
  rw [h0, mutualInfo_eq_entropy_sub_condEntropy' hν]
  have h1 := condEntropy_mixture w (fun i => bcJoint (q i) W)
    (fun _ (z : (𝒰 × α) × (β₁ × β₂)) => z.2.2) (fun _ z => z.1.1)
  have h2 := condEntropy_mixture w (fun i => bcJoint (q i) W)
    (fun _ (z : (𝒰 × α) × (β₁ × β₂)) => z.2.2) (fun _ _ => ())
  have h3 := condEntropy_le_entropy hν (fun t : ι × ((𝒰 × α) × (β₁ × β₂)) => t.2.2.2)
    (fun t => (t.1, ()))
  have h4 : ∑ i, w i * H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 | (fun _ => ()) ;
      bcJoint (q i) W] = ∑ i, w i * H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 ; bcJoint (q i) W] :=
    sum_congr rfl fun i _ => by rw [condEntropy_const (bcJoint_isPMF (hq i) hW)]
  have h5 : ∑ i, w i * bcInfoUY₂ (q i) W =
      ∑ i, w i * H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 ; bcJoint (q i) W] -
        ∑ i, w i * H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 | fun z => z.1.1 ; bcJoint (q i) W] := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [bcInfoUY₂, mutualInfo_eq_entropy_sub_condEntropy' (bcJoint_isPMF (hq i) hW), mul_sub]
  rw [h5]
  have h6 : H[fun t : ι × ((𝒰 × α) × (β₁ × β₂)) => t.2.2.2 | fun t => (t.1, t.2.1.1) ;
      fun z => w z.1 * bcJoint (q z.1) W z.2] = _ := h1
  have h7 : H[fun t : ι × ((𝒰 × α) × (β₁ × β₂)) => t.2.2.2 | fun t => (t.1, ()) ;
      fun z => w z.1 * bcJoint (q z.1) W z.2] = _ := h2
  rw [h6]
  rw [h7, h4] at h3
  linarith

/-- The law of `(e(U), X)` for a relabelling `e` of the auxiliary alphabet. -/
def degradedBCRelabelLaw (e : 𝒰 ≃ 𝒰') (q : 𝒰 × α → ℝ) : 𝒰' × α → ℝ := fun z => q (e.symm z.1, z.2)

omit [Fintype ι] in
lemma degradedBCRelabelLaw_isPMF (e : 𝒰 ≃ 𝒰')
    {q : 𝒰 × α → ℝ} (hq : IsPMF q) : IsPMF (degradedBCRelabelLaw e q) := by
  refine ⟨fun z => hq.nonneg _, ?_⟩
  have := (Equiv.prodCongr e.symm (Equiv.refl α)).sum_comp q
  rw [hq.sum_eq_one] at this
  exact this

omit [Fintype ι] [Fintype 𝒰'] in
private lemma dist_bcJoint_relabel [Finite 𝒰'] (e : 𝒰 ≃ 𝒰') (q : 𝒰 × α → ℝ) :
    dist (bcJoint q W) (Equiv.prodCongr (Equiv.prodCongr e (Equiv.refl α))
      (Equiv.refl (β₁ × β₂))) = bcJoint (degradedBCRelabelLaw e q) W := by
  have h := dist_comp_equiv (bcJoint (degradedBCRelabelLaw e q) W)
    (Equiv.prodCongr (Equiv.prodCongr e (Equiv.refl α)) (Equiv.refl (β₁ × β₂)))
  rw [← h]
  congr 1
  funext z
  simp [bcJoint, jointOf, degradedBCRelabelLaw]

omit [Fintype ι] in
lemma degradedBC_bcInfoXY₁U_relabel (e : 𝒰 ≃ 𝒰') {q : 𝒰 × α → ℝ} (hq : IsPMF q)
    (hW : IsChannel W) : bcInfoXY₁U (degradedBCRelabelLaw e q) W = bcInfoXY₁U q W := by
  have hμ := bcJoint_isPMF hq hW
  have h := condMutualInfo_comp hμ (Equiv.prodCongr (Equiv.prodCongr e (Equiv.refl α))
    (Equiv.refl (β₁ × β₂))) (fun t => t.1.2) (fun t => t.2.1) (fun t => t.1.1)
  rw [dist_bcJoint_relabel] at h
  refine h.symm.trans ?_
  have h1 : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2 | fun z => e z.1.1 ; bcJoint q W] =
      H[fun z => z.1.2 | fun z => z.1.1 ; bcJoint q W] :=
    condEntropy_congr_right hμ _ e e.injective fun _ => rfl
  have h2 : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.1.2 |
      pair (fun z => z.2.1) (fun z => e z.1.1) ; bcJoint q W] =
      H[fun z => z.1.2 | pair (fun z => z.2.1) (fun z => z.1.1) ; bcJoint q W] :=
    condEntropy_congr_right hμ _ (Prod.map id e) (Function.injective_id.prodMap e.injective)
      fun _ => rfl
  rw [bcInfoXY₁U, condMutualInfo, condMutualInfo, ← h1, ← h2]
  rfl

omit [Fintype ι] in
lemma degradedBC_bcInfoUY₂_relabel (e : 𝒰 ≃ 𝒰') {q : 𝒰 × α → ℝ} (hq : IsPMF q)
    (hW : IsChannel W) : bcInfoUY₂ (degradedBCRelabelLaw e q) W = bcInfoUY₂ q W := by
  have hμ := bcJoint_isPMF hq hW
  have h := mutualInfo_comp (μ := bcJoint q W)
    (Equiv.prodCongr (Equiv.prodCongr e (Equiv.refl α)) (Equiv.refl (β₁ × β₂)))
    (fun t => t.1.1) (fun t => t.2.2)
  rw [dist_bcJoint_relabel] at h
  refine h.symm.trans ?_
  have h1 : H[fun z : (𝒰 × α) × (β₁ × β₂) => z.2.2 | fun z => e z.1.1 ; bcJoint q W] =
      H[fun z => z.2.2 | fun z => z.1.1 ; bcJoint q W] :=
    condEntropy_congr_right hμ _ e e.injective fun _ => rfl
  rw [bcInfoUY₂, mutualInfo_eq_entropy_sub_condEntropy' hμ,
    mutualInfo_eq_entropy_sub_condEntropy' hμ, ← h1]
  rfl

end TimeSharing

end InfoTheory
