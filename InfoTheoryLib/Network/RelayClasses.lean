/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MACMultiLetter
public import InfoTheoryLib.Network.RelayDF

/-!
# The relay channel: classes with known capacity

The classes of relay channels of Lecture 17 of El Gamal and Kim whose capacity is known, because the
cutset bound and a form of partial decode–forward coincide.

## Main definitions

* `IsDegradedRC W`: physically degraded channels.
* `IsSemiDetRC W g`: semi-deterministic channels, with `Y₁ = g(X, X₁)`.
* `rcSemiInfo p W`: `H(Y₁ | X₁) + I(X; Y | X₁, Y₁)`.
* `rcDirectBound W`: the direct transmission lower bound.
* `IsReverselyDegradedRC W`: reversely degraded channels.
* `IsCascadeRC W κ₁ κ₂`: the cascade of two channels.

## Main statements

* `rcCapacity_eq`: the capacity from the two directions of a coding theorem.
* `rcCapacity_degraded`: the capacity of a physically degraded channel, page 17-18.
* `rcCapacity_semiDet`: the capacity of a semi-deterministic channel, page 17-35.
* `isAchievableRC_direct`: the direct transmission lower bound, page 17-9.
* `rcCapacity_reverselyDegraded`: the capacity of a reversely degraded channel, page 17-9.
* `rcCapacity_cascade`: the capacity of a cascade of two channels, page 17-10.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 17
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]
  {W : X × X₁ → Y × Y₁ → ℝ} {p : X × X₁ → ℝ}

omit [Fintype X] [Fintype X₁] in
/-- The capacity from the two directions of a coding theorem. -/
lemma rcCapacity_eq [Nonempty X] [Nonempty X₁] {V : ℝ}
    (h₁ : ∀ R, R * log 2 < V → IsAchievableRC W R) (h₂ : ∀ R, IsAchievableRC W R → R * log 2 ≤ V) :
    rcCapacity W = V / log 2 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨0, isAchievableRC_of_nonpos le_rfl⟩
    (fun R hR => (le_div_iff₀ hlog2).mpr (h₂ R hR)) fun a ha => ?_
  obtain ⟨b, hab, hb⟩ := exists_between ha
  exact ⟨b, h₁ b ((lt_div_iff₀ hlog2).mp hb), hab⟩

/-- **The chain rule on the broadcast cut**:
`I(X; Y, Y₁ | X₁) = I(X; Y₁ | X₁) + I(X; Y | X₁, Y₁)`. -/
lemma rcBcInfo_split (hp : IsPMF p) (hW : IsChannel W) :
    rcBcInfo p W = rcDfInfo p W + I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 |
      fun z => (z.1.2, z.2.2) ; jointOf p W] := by
  have hJ := jointOf_isPMF hp hW
  simp only [rcBcInfo, rcDfInfo]
  rw [condMutualInfo_eq_entropies hJ, condMutualInfo_eq_entropies hJ,
    condMutualInfo_eq_entropies hJ]
  have h₁ : H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) Prod.snd ; jointOf p W] =
      H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.2.2)) (fun z => z.2.1) ; jointOf p W] :=
    entropyRV_eq_of_injective _ (fun t : (X₁ × Y₁) × Y => (t.1.1, (t.2, t.1.2)))
      (fun a b h => by
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg (fun t => t.2.1) h
        have h₃ := congrArg (fun t => t.2.2) h
        exact Prod.ext (Prod.ext h₁ h₃) h₂) fun _ => rfl
  have h₂ : H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) Prod.snd) (fun z => z.1.1) ;
      jointOf p W] = H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.2.2)) (fun z => z.2.1))
        (fun z => z.1.1) ; jointOf p W] :=
    entropyRV_eq_of_injective _ (fun t : ((X₁ × Y₁) × Y) × X => ((t.1.1.1, (t.1.2, t.1.1.2)), t.2))
      (fun a b h => by
        have h₁ := congrArg (fun t => t.1.1) h
        have h₂ := congrArg (fun t => t.1.2.1) h
        have h₃ := congrArg (fun t => t.1.2.2) h
        have h₄ := congrArg Prod.snd h
        exact Prod.ext (Prod.ext (Prod.ext h₁ h₃) h₂) h₄) fun _ => rfl
  have h₃ : H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => z.2.2) ; jointOf p W] =
      H[fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.2.2) ; jointOf p W] := rfl
  have h₄ : H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => z.2.2)) (fun z => z.1.1) ;
      jointOf p W] = H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.2.2)) (fun z => z.1.1) ;
        jointOf p W] := rfl
  rw [h₁, h₂, h₃, h₄]
  ring

/-! ### Physically degraded channels -/

/-- **Page 17-18 of [elgamal2010].** A physically degraded relay channel:
`p(y, y₁ | x, x₁) = p(y₁ | x, x₁) p(y | y₁, x₁)`. -/
def IsDegradedRC (W : X × X₁ → Y × Y₁ → ℝ) : Prop :=
  ∃ κ₂ : X₁ × Y₁ → Y → ℝ, IsChannel κ₂ ∧ ∀ a y y₁, W a (y, y₁) = bcMarg₂ W a y₁ * κ₂ (a.2, y₁) y

/-- For a degraded channel, `I(X; Y | X₁, Y₁) = 0`. -/
lemma condMutualInfo_degraded_eq_zero (hd : IsDegradedRC W) (hp : IsPMF p) (hW : IsChannel W) :
    I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 | fun z => (z.1.2, z.2.2) ;
      jointOf p W] = 0 := by
  classical
  obtain ⟨κ₂, hκ, hfac⟩ := hd
  have hJ := jointOf_isPMF hp hW
  rw [condMutualInfo_comm hJ, condMutualInfo_eq' hJ, sub_eq_zero]
  let C : (X × X₁) × (Y × Y₁) → X₁ × Y₁ := fun z => (z.1.2, z.2.2)
  let A : (X × X₁) × (Y × Y₁) → (X₁ × Y₁) × X := pair C fun z => z.1.1
  have hinj : Function.Injective (pair A fun z : (X × X₁) × (Y × Y₁) => z.2.1) := fun a b h => by
    have h₁ := congrArg (fun t => t.1.1.1) h
    have h₂ := congrArg (fun t => t.1.1.2) h
    have h₃ := congrArg (fun t => t.1.2) h
    have h₄ := congrArg Prod.snd h
    exact Prod.ext (Prod.ext h₃ h₁) (Prod.ext h₄ h₂)
  have hkey := condEntropy_eq_comp_of_channel hJ A (fun z => z.2.1) (Prod.fst : (X₁ × Y₁) × X → _)
    hκ (by
      funext ⟨⟨⟨x₁, y₁⟩, x⟩, y⟩
      have h₁ := dist_comp_of_injective (jointOf p W) id hinj ((x, x₁), (y, y₁))
      rw [dist_id] at h₁
      have e₁ : dist (jointOf p W) (pair A fun z => z.2.1) (((x₁, y₁), x), y) =
          jointOf p W ((x, x₁), (y, y₁)) := h₁
      have hA : dist (jointOf p W) A ((x₁, y₁), x) = p (x, x₁) * bcMarg₂ W (x, x₁) y₁ := by
        have hm : A = (fun t : Y × ((X₁ × Y₁) × X) => t.2) ∘ pair (fun z => z.2.1) A := rfl
        have hsum : dist (jointOf p W) A ((x₁, y₁), x) =
            ∑ y', jointOf p W ((x, x₁), (y', y₁)) := by
          simp only [dist]
          rw [Fintype.sum_prod_type]
          simp only [Fintype.sum_prod_type]
          rw [Finset.sum_eq_single x, Finset.sum_eq_single x₁]
          · rw [sum_comm, Finset.sum_eq_single y₁]
            · refine sum_congr rfl fun y' _ => ?_
              simp [A, C]
            · intro y₁' _ h
              refine sum_eq_zero fun y' _ => ite_eq_right fun he => h ?_
              exact (Prod.ext_iff.mp (Prod.ext_iff.mp he).1).2
            · simp
          · intro x₁' _ h
            refine sum_eq_zero fun y' _ => sum_eq_zero fun y₁' _ => ite_eq_right fun he => h ?_
            exact (Prod.ext_iff.mp (Prod.ext_iff.mp he).1).1
          · simp
          · intro x' _ h
            refine sum_eq_zero fun x₁' _ => sum_eq_zero fun y' _ => sum_eq_zero fun y₁' _ =>
              ite_eq_right fun he => h ?_
            exact (Prod.ext_iff.mp he).2
          · simp
        rw [hsum]
        simp only [jointOf, bcMarg₂, mul_sum]
      simp only [jointOf]
      rw [e₁, hA]
      simp only [jointOf]
      rw [hfac (x, x₁) y y₁]
      ring)
  have e₁ : H[fun z : (X × X₁) × (Y × Y₁) => z.2.1 | A ; jointOf p W] = H[fun z => z.2.1 | C ;
      jointOf p W] := hkey
  exact e₁.symm

/-- For a degraded channel the broadcast cut is the decode–forward term. -/
lemma rcBcInfo_degraded (hd : IsDegradedRC W) (hp : IsPMF p) (hW : IsChannel W) :
    rcBcInfo p W = rcDfInfo p W := by
  rw [rcBcInfo_split hp hW, condMutualInfo_degraded_eq_zero hd hp hW, add_zero]

/-- **Page 17-18 of [elgamal2010].** The capacity of a physically degraded relay channel is the
decode–forward lower bound. -/
theorem rcCapacity_degraded [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]
    (hd : IsDegradedRC W) (hW : IsChannel W) : rcCapacity W = rcDfBound W / log 2 := by
  refine rcCapacity_eq (fun R hR => isAchievableRC_of_lt_rcDfBound hW hR) fun R hR => ?_
  have h := hR.le_rcCutsetBound hW
  have hset : rcCutsetBound W = rcDfBound W := by
    simp only [rcCutsetBound, rcDfBound]
    congr 1
    ext v
    refine exists_congr fun q => and_congr_right fun hq => ?_
    rw [rcBcInfo_degraded hd hq hW]
  rwa [hset] at h

/-! ### Semi-deterministic channels -/

/-- **Page 17-35 of [elgamal2010].** A semi-deterministic relay channel: `Y₁ = g(X, X₁)`. -/
def IsSemiDetRC (W : X × X₁ → Y × Y₁ → ℝ) (g : X × X₁ → Y₁) : Prop :=
  ∀ a y y₁, W a (y, y₁) ≠ 0 → y₁ = g a

/-- `H(Y₁ | X₁) + I(X; Y | X₁, Y₁)`, in nats. -/
def rcSemiInfo (p : X × X₁ → ℝ) (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  H[fun z : (X × X₁) × (Y × Y₁) => z.2.2 | fun z => z.1.2 ; jointOf p W] +
    I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 | fun z => (z.1.2, z.2.2) ; jointOf p W]

/-- **Page 17-35 of [elgamal2010].** The expression of the capacity of a semi-deterministic relay
channel, in nats. -/
def rcSemiBound (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  sSup {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧ v = min (rcMacInfo p W) (rcSemiInfo p W)}

omit [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁] in
/-- On the support of the joint law, `Y₁ = g(X, X₁)`. -/
lemma jointOf_ne_zero_semi {g : X × X₁ → Y₁} (hg : IsSemiDetRC W g)
    {z : (X × X₁) × (Y × Y₁)} (hz : jointOf p W z ≠ 0) : z.2.2 = g z.1 :=
  hg z.1 z.2.1 z.2.2 (right_ne_zero_of_mul hz)

/-- On the support of the joint law, `g(X, X₁)` can be replaced by `Y₁` in an entropy. -/
lemma entropy_semi_ae {T : Type*} [Fintype T] {g : X × X₁ → Y₁} (hg : IsSemiDetRC W g)
    (F : Y₁ → (X × X₁) × (Y × Y₁) → T) :
    H[fun z => F (g z.1) z ; jointOf p W] = H[fun z => F z.2.2 z ; jointOf p W] := by
  rw [entropyRV, entropyRV]
  congr 1
  refine dist_congr_of_ae fun z hz => ?_
  rw [jointOf_ne_zero_semi hg hz]

/-- For `U = g(X, X₁) = Y₁`, the expression of partial decode–forward is the one of the capacity. -/
lemma rcFunInfo_semi {g : X × X₁ → Y₁} (hg : IsSemiDetRC W g) (hp : IsPMF p) (hW : IsChannel W) :
    rcFunInfo p g W = rcSemiInfo p W := by
  have hJ := jointOf_isPMF hp hW
  simp only [rcFunInfo, rcSemiInfo]
  congr 1
  · rw [condMutualInfo_eq_entropies hJ, condEntropy_eq_sub hJ]
    have h₁ : H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => g z.1) ; jointOf p W] =
        H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => z.2.2) ; jointOf p W] :=
      entropy_semi_ae hg fun y₁ z => (z.1.2, y₁)
    have h₂ : H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => z.2.2))
        (fun z => g z.1) ; jointOf p W] = H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2)
          (fun z => z.2.2) ; jointOf p W] := by
      have h₃ := entropy_semi_ae (p := p) hg fun y₁ z => ((z.1.2, z.2.2), y₁)
      refine h₃.trans ?_
      exact entropyRV_eq_of_injective _ (fun t : X₁ × Y₁ => (t, t.2))
        (fun a b h => congrArg Prod.fst h) fun _ => rfl
    rw [h₁, h₂]
    ring
  · rw [condMutualInfo_eq_entropies hJ, condMutualInfo_eq_entropies hJ]
    have h₁ : H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, g z.1)) (fun z => z.1.1) ;
        jointOf p W] = H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.2.2)) (fun z => z.1.1) ;
          jointOf p W] := entropy_semi_ae hg fun y₁ z => ((z.1.2, y₁), z.1.1)
    have h₂ : H[fun z : (X × X₁) × (Y × Y₁) => (z.1.2, g z.1) ; jointOf p W] =
        H[fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.2.2) ; jointOf p W] :=
      entropy_semi_ae hg fun y₁ z => (z.1.2, y₁)
    have h₃ : H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, g z.1)) (fun z => z.2.1))
        (fun z => z.1.1) ; jointOf p W] = H[pair (pair (fun z : (X × X₁) × (Y × Y₁) =>
          (z.1.2, z.2.2)) (fun z => z.2.1)) (fun z => z.1.1) ; jointOf p W] :=
      entropy_semi_ae hg fun y₁ z => (((z.1.2, y₁), z.2.1), z.1.1)
    have h₄ : H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, g z.1)) (fun z => z.2.1) ;
        jointOf p W] = H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, z.2.2)) (fun z => z.2.1) ;
          jointOf p W] := entropy_semi_ae hg fun y₁ z => ((z.1.2, y₁), z.2.1)
    rw [h₁, h₂, h₃, h₄]

/-- **Page 17-35 of [elgamal2010].** The capacity of a semi-deterministic relay channel. -/
theorem rcCapacity_semiDet [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁] {g : X × X₁ → Y₁}
    (hg : IsSemiDetRC W g) (hW : IsChannel W) : rcCapacity W = rcSemiBound W / log 2 := by
  refine rcCapacity_eq (fun R hR => ?_) fun R hR => ?_
  · have hne : {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧ v =
    min (rcMacInfo p W) (rcSemiInfo p W)}.Nonempty :=
      ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩
    obtain ⟨_, ⟨p, hp, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne hR
    exact isAchievableRC_of_fun hp hW g (hv.trans_le (min_le_left _ _))
      (by rw [rcFunInfo_semi hg hp hW]; exact hv.trans_le (min_le_right _ _))
  · have h := hR.le_rcCutsetBound hW
    refine h.trans (csSup_le ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩ fun v hv => ?_)
    obtain ⟨p, hp, rfl⟩ := hv
    have hbdd : BddAbove {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧
        v = min (rcMacInfo p W) (rcSemiInfo p W)} := by
      refine ⟨capacity (bcMarg₁ W), ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact (min_le_left _ _).trans (mutualInfoOf_le_capacity hq hW.bcMarg₁)
    refine le_trans ?_ (le_csSup hbdd ⟨p, hp, rfl⟩)
    refine min_le_min le_rfl ?_
    have hJ := jointOf_isPMF hp hW
    rw [rcBcInfo_split hp hW, rcSemiInfo]
    refine add_le_add ?_ le_rfl
    rw [rcDfInfo, condMutualInfo_comm hJ, condMutualInfo_eq' hJ]
    linarith [condEntropy_nonneg hJ (fun z : (X × X₁) × (Y × Y₁) => z.2.2)
      (pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) fun z => z.1.1)]

/-! ### Direct transmission -/

/-- **Page 17-9 of [elgamal2010].** The direct transmission lower bound
`max_{p(x), x₁} I(X; Y | X₁ = x₁)`, in nats. -/
def rcDirectBound (W : X × X₁ → Y × Y₁ → ℝ) : ℝ :=
  sSup {v | ∃ (q : X → ℝ) (x₁ : X₁), IsPMF q ∧ v = mutualInfoOf q fun x => bcMarg₁ W (x, x₁)}

omit [Fintype X₁] in
/-- **Page 17-9 of [elgamal2010].** Direct transmission, with a constant relay input. -/
theorem isAchievableRC_direct [Finite X₁] [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]
    {q : X → ℝ} (hq : IsPMF q) (x₀ : X₁) (hW : IsChannel W) {R : ℝ}
    (h : R * log 2 < mutualInfoOf q fun x => bcMarg₁ W (x, x₀)) : IsAchievableRC W R := by
  classical
  have : Fintype X₁ := Fintype.ofFinite X₁
  let g : X → X × X₁ := fun x => (x, x₀)
  let p₀ : X × X₁ → ℝ := dist q g
  have hp : IsPMF p₀ := hq.dist g
  have hJ := jointOf_isPMF hp hW
  have hmac : rcMacInfo p₀ W = mutualInfoOf q fun x => bcMarg₁ W (x, x₀) :=
    (mutualInfoOf_comp hq hW.bcMarg₁ g).symm
  have hae : ∀ z : (X × X₁) × (Y × Y₁), jointOf p₀ W z ≠ 0 → z.1.2 = x₀ := by
    intro z hz
    have h₁ : p₀ z.1 ≠ 0 := left_ne_zero_of_mul hz
    by_contra hne
    refine h₁ ?_
    simp only [p₀, dist]
    exact sum_eq_zero fun x _ => ite_eq_right fun he => hne (by rw [← he])
  have hfun : rcMacInfo p₀ W ≤ rcFunInfo p₀ (fun _ => ()) W := by
    rw [rcMacInfo_eq]
    have hrw : I[Prod.fst : fun z : (X × X₁) × (Y × Y₁) => z.2.1 ; jointOf p₀ W] =
        I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 |
          fun z => (z.1.2, ()) ; jointOf p₀ W] := by
      rw [mutualInfo_eq_add_sub hJ, condMutualInfo_eq_entropies hJ]
      have e₁ : H[Prod.fst ; jointOf p₀ W] = H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, ()))
          (fun z => z.1.1) ; jointOf p₀ W] := by
        refine entropyRV_eq_of_injective _ (fun t : (X₁ × Unit) × X => (t.2, t.1.1))
          (fun a b h => ?_) fun _ => rfl
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        exact Prod.ext (Prod.ext h₂ rfl) h₁
      have e₂ : H[fun z : (X × X₁) × (Y × Y₁) => (z.1.2, ()) ; jointOf p₀ W] = 0 := by
        have hd : dist (jointOf p₀ W) (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, ())) =
            dist (jointOf p₀ W) fun _ => (x₀, ()) :=
          dist_congr_of_ae fun z hz => by rw [hae z hz]
        rw [entropyRV, hd]
        exact entropyRV_const hJ (x₀, ())
      have e₃ : H[pair Prod.fst (fun z : (X × X₁) × (Y × Y₁) => z.2.1) ; jointOf p₀ W] =
          H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, ())) (fun z => z.2.1))
            (fun z => z.1.1) ; jointOf p₀ W] := by
        refine entropyRV_eq_of_injective _ (fun t : ((X₁ × Unit) × Y) × X => ((t.2, t.1.1.1),
          t.1.2))
          (fun a b h => ?_) fun _ => rfl
        have h₁ := congrArg (fun t => t.1.1) h
        have h₂ := congrArg (fun t => t.1.2) h
        have h₃ := congrArg Prod.snd h
        exact Prod.ext (Prod.ext (Prod.ext h₂ rfl) h₃) h₁
      have e₄ : H[fun z : (X × X₁) × (Y × Y₁) => z.2.1 ; jointOf p₀ W] =
          H[pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, ())) (fun z => z.2.1) ; jointOf p₀ W] := by
        rw [entropyRV, entropyRV]
        have : dist (jointOf p₀ W) (pair (fun z : (X × X₁) × (Y × Y₁) => (z.1.2, ()))
            (fun z => z.2.1)) = dist (jointOf p₀ W) (pair (fun _ : (X × X₁) × (Y × Y₁) => (x₀, ()))
              (fun z => z.2.1)) := dist_congr_of_ae fun z hz => by simp [pair, hae z hz]
        rw [this]
        exact (entropyRV_eq_of_injective _ (fun y : Y => ((x₀, ()), y))
          (fun a b h => congrArg Prod.snd h) fun _ => rfl).symm
      rw [e₁, e₂, e₃, e₄]
      ring
    rw [hrw, rcFunInfo]
    linarith [condMutualInfo_nonneg hJ (fun z : (X × X₁) × (Y × Y₁) => ())
      (fun z => z.2.2) (fun z => z.1.2)]
  rw [← hmac] at h
  exact isAchievableRC_of_fun hp hW (fun _ => ()) h (h.trans_le hfun)

/-! ### Reversely degraded channels -/

/-- **Page 17-9 of [elgamal2010].** A reversely degraded relay channel:
`p(y, y₁ | x, x₁) = p(y | x, x₁) p(y₁ | y, x₁)`. -/
def IsReverselyDegradedRC (W : X × X₁ → Y × Y₁ → ℝ) : Prop :=
  ∃ κ₂ : X₁ × Y → Y₁ → ℝ, IsChannel κ₂ ∧ ∀ a y y₁, W a (y, y₁) = bcMarg₁ W a y * κ₂ (a.2, y) y₁

/-- The relay channel with the two outputs exchanged. -/
def rcSwap (W : X × X₁ → Y × Y₁ → ℝ) : X × X₁ → Y₁ × Y → ℝ := fun a o => W a (o.2, o.1)

omit [Fintype X] [Fintype X₁] in
lemma rcSwap_isChannel (hW : IsChannel W) : IsChannel (rcSwap W) := by
  intro a
  refine ⟨fun o => (hW a).nonneg _, ?_⟩
  have h := (hW a).sum_eq_one
  rw [Fintype.sum_prod_type] at h ⊢
  rw [sum_comm]
  exact h

/-- The joint law of the channel with the outputs exchanged. -/
lemma jointOf_rcSwap (p : X × X₁ → ℝ) :
    jointOf p (rcSwap W) = dist (jointOf p W) fun z => (z.1, (z.2.2, z.2.1)) := by
  classical
  have hinj : Function.Injective fun z : (X × X₁) × (Y × Y₁) => (z.1, (z.2.2, z.2.1)) :=
    fun a b h => by
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg (fun t => t.2.1) h
      have h₃ := congrArg (fun t => t.2.2) h
      exact Prod.ext h₁ (Prod.ext h₃ h₂)
  funext ⟨a, y₁, y⟩
  have := dist_comp_of_injective (jointOf p W) id hinj (a, (y, y₁))
  rw [dist_id] at this
  exact this.symm

/-- For a reversely degraded channel the broadcast cut is `I(X; Y | X₁)`. -/
lemma rcBcInfo_reverselyDegraded (hd : IsReverselyDegradedRC W) (hp : IsPMF p) (hW : IsChannel W) :
    rcBcInfo p W = I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 | fun z => z.1.2 ;
      jointOf p W] := by
  have hJ := jointOf_isPMF hp hW
  have hs := rcSwap_isChannel hW
  obtain ⟨κ₂, hκ, hfac⟩ := hd
  have hd' : IsDegradedRC (rcSwap W) := ⟨κ₂, hκ, fun a y' y₁' => hfac a y₁' y'⟩
  have h₁ := rcBcInfo_degraded hd' hp hs
  have h₂ : rcBcInfo p (rcSwap W) = rcBcInfo p W := by
    simp only [rcBcInfo]
    rw [jointOf_rcSwap, condMutualInfo_dist hJ, condMutualInfo_eq_entropies hJ,
      condMutualInfo_eq_entropies hJ]
    have e₁ : H[pair (Prod.snd ∘ fun z : (X × X₁) × (Y × Y₁) => z.1) (Prod.fst ∘ fun z => z.1) ∘
        id ; jointOf p W] = H[pair (Prod.snd ∘ fun z : (X × X₁) × (Y × Y₁) => z.1)
          (Prod.fst ∘ fun z => z.1) ∘ id ; jointOf p W] := rfl
    have e₂ : H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => (z.2.2, z.2.1)) ;
        jointOf p W] = H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) Prod.snd ; jointOf p W] :=
      entropyRV_eq_of_injective _ (fun t : X₁ × (Y × Y₁) => (t.1, (t.2.2, t.2.1)))
        (fun a b h => by
          have h₁ := congrArg Prod.fst h
          have h₂ := congrArg (fun t => t.2.1) h
          have h₃ := congrArg (fun t => t.2.2) h
          exact Prod.ext h₁ (Prod.ext h₃ h₂)) fun _ => rfl
    have e₃ : H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => (z.2.2, z.2.1)))
        (fun z => z.1.1) ; jointOf p W] = H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2)
          Prod.snd) (fun z => z.1.1) ; jointOf p W] :=
      entropyRV_eq_of_injective _ (fun t : (X₁ × (Y × Y₁)) × X => ((t.1.1, (t.1.2.2, t.1.2.1)),
        t.2))
        (fun a b h => by
          have h₁ := congrArg (fun t => t.1.1) h
          have h₂ := congrArg (fun t => t.1.2.1) h
          have h₃ := congrArg (fun t => t.1.2.2) h
          have h₄ := congrArg Prod.snd h
          exact Prod.ext (Prod.ext h₁ (Prod.ext h₃ h₂)) h₄) fun _ => rfl
    change H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => z.1.1) ; jointOf p W] -
        H[fun z : (X × X₁) × (Y × Y₁) => z.1.2 ; jointOf p W] -
        H[pair (pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => (z.2.2, z.2.1)))
          (fun z => z.1.1) ; jointOf p W] +
        H[pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => (z.2.2, z.2.1)) ; jointOf p W] = _
    rw [e₂, e₃]
  rw [← h₂, h₁, rcDfInfo, jointOf_rcSwap, condMutualInfo_dist hJ]
  rfl

/-- `I(X; Y | X₁)` is at most the direct transmission bound. -/
lemma condMutualInfo_le_rcDirectBound [Nonempty X] (hp : IsPMF p) (hW : IsChannel W) :
    I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 | fun z => z.1.2 ; jointOf p W] ≤
      rcDirectBound W := by
  classical
  have hJ := jointOf_isPMF hp hW
  have hV := hW.bcMarg₁
  set V := bcMarg₁ W with hVdef
  have hbdd : BddAbove {v | ∃ (q : X → ℝ) (x₁ : X₁), IsPMF q ∧
      v = mutualInfoOf q fun x => bcMarg₁ W (x, x₁)} := by
    refine ⟨Real.log (Fintype.card Y), ?_⟩
    rintro _ ⟨q, x₁, hq, rfl⟩
    exact (mutualInfoOf_le_capacity hq fun x => hV (x, x₁)).trans
      (capacity_le_log_card_output fun x => hV (x, x₁))
  -- on the law of `((X, X₁), Y)`
  let T : (X × X₁) × (Y × Y₁) → (X × X₁) × Y := fun z => (z.1, z.2.1)
  have hd : dist (jointOf p W) T = jointOf p V := by
    funext ⟨a, y⟩
    rw [show T = pair Prod.fst fun z => (Prod.snd z).1 from rfl, dist_pair_marg_fst,
      dist_pair_fst_snd]
    simp only [jointOf, hVdef, bcMarg₁, mul_sum]
  have hμ := jointOf_isPMF hp hV
  have e₀ : I[fun z : (X × X₁) × (Y × Y₁) => z.1.1 : fun z => z.2.1 | fun z => z.1.2 ;
      jointOf p W] = I[fun z : (X × X₁) × Y => z.1.1 : Prod.snd | fun z => z.1.2 ;
        jointOf p V] := by
    rw [← hd, condMutualInfo_dist hJ]
    rfl
  rw [e₀, condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
  -- the two conditional entropies
  let p₁ : X₁ → ℝ := fun s => ∑ x, p (x, s)
  have hp₁ : ∀ s, dist (jointOf p V) (fun z => z.1.2) s = p₁ s := by
    intro s
    have e : (fun z : (X × X₁) × Y => z.1.2) = (Prod.snd ∘ Prod.fst) := rfl
    rw [e, dist_comp_eq, dist_jointOf_fst hV]
    simp only [dist, p₁, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    exact (Finset.sum_eq_single s (fun b _ hb => ite_eq_right hb) (by simp)).trans (ite_eq_left rfl)
  have hsum₁ : ∑ s, p₁ s = 1 := by
    have := hp.sum_eq_one
    rw [Fintype.sum_prod_type] at this
    rw [sum_comm]
    exact this
  have hp₁0 : ∀ s, 0 ≤ p₁ s := fun s => sum_nonneg fun x _ => hp.nonneg _
  have hpair : ∀ s y, dist (jointOf p V) (pair (fun z => z.1.2) Prod.snd) (s, y) =
      ∑ x, p (x, s) * V (x, s) y := by
    intro s y
    simp only [dist, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single s, Finset.sum_eq_single y]
    · simp [pair, jointOf]
    · intro y' _ h
      refine ite_eq_right fun he => h ?_
      exact congrArg Prod.snd he
    · simp
    · intro s' _ h
      refine sum_eq_zero fun y' _ => ite_eq_right fun he => h ?_
      exact congrArg Prod.fst he
    · simp
  have hsecond : H[Prod.snd | pair (fun z : (X × X₁) × Y => z.1.2) (fun z => z.1.1) ; jointOf p V] =
      ∑ a, p a * entropy (V a) := by
    have hc := condEntropy_jointOf hp hV
    rw [← hc]
    refine condEntropy_congr_right hμ _ (fun t : X × X₁ => (t.2, t.1)) (fun a b h => ?_) fun _ =>
      rfl
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hterm : ∀ s, p₁ s * condEntropyAt (jointOf p V) Prod.snd (fun z => z.1.2) s -
      ∑ x, p (x, s) * entropy (V (x, s)) ≤ p₁ s * rcDirectBound W := by
    intro s
    by_cases hs : p₁ s = 0
    · have h0 : ∀ x, p (x, s) = 0 := fun x =>
        (sum_eq_zero_iff_of_nonneg fun x _ => hp.nonneg _).mp hs x (mem_univ x)
      simp [hs, h0]
    have hspos : 0 < p₁ s := lt_of_le_of_ne (hp₁0 s) (Ne.symm hs)
    let q : X → ℝ := fun x => p (x, s) / p₁ s
    have hq : IsPMF q := by
      refine ⟨fun x => div_nonneg (hp.nonneg _) hspos.le, ?_⟩
      simp only [q]
      rw [← sum_div]
      exact div_self hs
    have hcond : condDist (jointOf p V) Prod.snd (fun z => z.1.2) s =
        outDist q fun x => V (x, s) := by
      funext y
      simp only [condDist, hpair, hp₁, outDist, q, sum_div]
      refine sum_congr rfl fun x _ => ?_
      ring
    have hI := mutualInfoOf_eq hq fun x => hV (x, s)
    have hle : mutualInfoOf q (fun x => V (x, s)) ≤ rcDirectBound W :=
      le_csSup hbdd ⟨q, s, hq, rfl⟩
    have heq : p₁ s * condEntropyAt (jointOf p V) Prod.snd (fun z => z.1.2) s -
        ∑ x, p (x, s) * entropy (V (x, s)) = p₁ s * mutualInfoOf q fun x => V (x, s) := by
      rw [hI, condEntropyAt, hcond, mul_sub, mul_sum]
      congr 1
      refine sum_congr rfl fun x _ => ?_
      simp only [q]
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hle hspos.le
  rw [hsecond, condEntropy]
  simp_rw [hp₁]
  calc _ = ∑ s, (p₁ s * condEntropyAt (jointOf p V) Prod.snd (fun z => z.1.2) s -
        ∑ x, p (x, s) * entropy (V (x, s))) := by
        rw [sum_sub_distrib, Fintype.sum_prod_type, sum_comm (s := univ) (t := univ)]
    _ ≤ ∑ s, p₁ s * rcDirectBound W := sum_le_sum fun s _ => hterm s
    _ = _ := by rw [← sum_mul, hsum₁, one_mul]

omit [Fintype X₁] in
/-- **Page 17-9 of [elgamal2010].** The capacity of a reversely degraded relay channel is the direct
transmission lower bound. -/
theorem rcCapacity_reverselyDegraded [Finite X₁] [Nonempty X] [Nonempty X₁] [Nonempty Y]
    [Nonempty Y₁] (hd : IsReverselyDegradedRC W) (hW : IsChannel W) :
    rcCapacity W = rcDirectBound W / log 2 := by
  have : Fintype X₁ := Fintype.ofFinite X₁
  refine rcCapacity_eq (fun R hR => ?_) fun R hR => ?_
  · have hne : {v | ∃ (q : X → ℝ) (x₁ : X₁), IsPMF q ∧
        v = mutualInfoOf q fun x => bcMarg₁ W (x, x₁)}.Nonempty :=
      ⟨_, uniformPMF _, Classical.arbitrary _, uniformPMF_isPMF, rfl⟩
    obtain ⟨_, ⟨q, x₁, hq, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne hR
    exact isAchievableRC_direct hq x₁ hW hv
  · refine (hR.le_rcCutsetBound hW).trans (csSup_le ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩ ?_)
    rintro _ ⟨q, hq, rfl⟩
    refine (min_le_right _ _).trans ?_
    rw [rcBcInfo_reverselyDegraded hd hq hW]
    exact condMutualInfo_le_rcDirectBound hq hW

/-! ### Cascades -/

/-- **Page 17-10 of [elgamal2010].** The cascade of two channels:
`p(y, y₁ | x, x₁) = p(y₁ | x) p(y | x₁)`. -/
def IsCascadeRC (W : X × X₁ → Y × Y₁ → ℝ) (κ₁ : X → Y₁ → ℝ) (κ₂ : X₁ → Y → ℝ) : Prop :=
  ∀ a y y₁, W a (y, y₁) = κ₁ a.1 y₁ * κ₂ a.2 y

section Cascade

variable {κ₁ : X → Y₁ → ℝ} {κ₂ : X₁ → Y → ℝ}

/-- The entropy of a function of each of two independent parts. -/
lemma entropy_prod_parts {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    {ν₁ : A → ℝ} {ν₂ : B → ℝ} (h₁ : IsPMF ν₁) (h₂ : IsPMF ν₂) (u : A → C) (v : B → D) :
    H[fun w : A × B => (u w.1, v w.2) ; prodDist ν₁ ν₂] = H[u ; ν₁] + H[v ; ν₂] := by
  rw [entropyRV, dist_prodDist_map, entropy_prodDist (h₁.dist u) (h₂.dist v)]
  rfl

/-- The joint law of a cascade, for a product of input laws. -/
lemma jointOf_cascade (h : IsCascadeRC W κ₁ κ₂) (q₁ : X → ℝ) (q₂ : X₁ → ℝ) :
    jointOf (prodDist q₁ q₂) W = dist (prodDist (jointOf q₁ κ₁) (jointOf q₂ κ₂))
      fun w => ((w.1.1, w.2.1), (w.2.2, w.1.2)) := by
  classical
  have hinj : Function.Injective fun w : (X × Y₁) × (X₁ × Y) =>
      ((w.1.1, w.2.1), (w.2.2, w.1.2)) := fun a b he => by
    have h₁ := congrArg (fun t => t.1.1) he
    have h₂ := congrArg (fun t => t.1.2) he
    have h₃ := congrArg (fun t => t.2.1) he
    have h₄ := congrArg (fun t => t.2.2) he
    exact Prod.ext (Prod.ext h₁ h₄) (Prod.ext h₂ h₃)
  funext ⟨⟨x, x₁⟩, y, y₁⟩
  have := dist_comp_of_injective (prodDist (jointOf q₁ κ₁) (jointOf q₂ κ₂)) id hinj
    ((x, y₁), (x₁, y))
  rw [dist_id] at this
  refine Eq.trans ?_ this.symm
  simp only [jointOf, prodDist, h (x, x₁) y y₁]
  ring

/-- **Page 17-10 of [elgamal2010].** The capacity of the cascade of two channels. -/
theorem rcCapacity_cascade [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]
    (h : IsCascadeRC W κ₁ κ₂) (h₁ : IsChannel κ₁) (h₂ : IsChannel κ₂) (hW : IsChannel W) :
    rcCapacity W = min (capacity κ₂) (capacity κ₁) / log 2 := by
  classical
  have hm₁ : ∀ a, bcMarg₁ W a = κ₂ a.2 := fun a => by
    funext y
    simp only [bcMarg₁, h a y, ← sum_mul, (h₁ a.1).sum_eq_one, one_mul]
  have hm₂ : ∀ a, bcMarg₂ W a = κ₁ a.1 := fun a => by
    funext y₁
    simp only [bcMarg₂, h a _ y₁, ← mul_sum, (h₂ a.2).sum_eq_one, mul_one]
  have hdeg : IsDegradedRC W := ⟨fun t => κ₂ t.1, fun t => h₂ t.1, fun a y y₁ => by
    rw [hm₂, h a y y₁]⟩
  refine rcCapacity_eq (fun R hR => ?_) fun R hR => ?_
  · obtain ⟨q₂, hq₂, hc₂⟩ := exists_capacity_eq h₂
    obtain ⟨q₁, hq₁, hc₁⟩ := exists_capacity_eq h₁
    have hν₁ := jointOf_isPMF hq₁ h₁
    have hν₂ := jointOf_isPMF hq₂ h₂
    have hPi : IsPMF (prodDist (jointOf q₁ κ₁) (jointOf q₂ κ₂)) := hν₁.prodDist hν₂
    have hp : IsPMF (prodDist q₁ q₂) := hq₁.prodDist hq₂
    have hJ := jointOf_cascade h q₁ q₂
    have hIy : I[fun z : (X × X₁) × (Y × Y₁) => z.1.2 : fun z => z.2.1 ;
        jointOf (prodDist q₁ q₂) W] = capacity κ₂ := by
      rw [← hc₂, mutualInfoOf]
      refine mutualInfo_eq_of_dist_pair_eq ?_
      rw [dist_pair_fst_snd, hJ]
      have e : pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) (fun z => z.2.1) ∘
          (fun w : (X × Y₁) × (X₁ × Y) => ((w.1.1, w.2.1), (w.2.2, w.1.2))) = Prod.snd := rfl
      rw [← dist_comp_eq, e]
      exact dist_prodDist_snd hν₁ (jointOf q₂ κ₂)
    have hDf : rcDfInfo (prodDist q₁ q₂) W = capacity κ₁ := by
      rw [← hc₁, rcDfInfo, hJ, condMutualInfo_dist hPi, condMutualInfo_eq_entropies hPi,
        mutualInfoOf, mutualInfo_eq_add_sub hν₁]
      have e₁ := entropy_prod_parts hν₁ hν₂ (fun t : X × Y₁ => t.1) (fun t : X₁ × Y => t.1)
      have e₂ := entropy_prod_parts hν₁ hν₂ (fun _ : X × Y₁ => ()) (fun t : X₁ × Y => t.1)
      have e₃ := entropy_prod_parts hν₁ hν₂ (fun t : X × Y₁ => t) (fun t : X₁ × Y => t.1)
      have e₄ := entropy_prod_parts hν₁ hν₂ (fun t : X × Y₁ => t.2) (fun t : X₁ × Y => t.1)
      have z₁ : H[fun _ : X × Y₁ => () ; jointOf q₁ κ₁] = 0 := entropyRV_const hν₁ _
      set Pi := prodDist (jointOf q₁ κ₁) (jointOf q₂ κ₂) with hPidef
      let R : (X × Y₁) × (X₁ × Y) → (X × X₁) × (Y × Y₁) :=
        fun w => ((w.1.1, w.2.1), (w.2.2, w.1.2))
      have i₁ : H[pair ((fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R)
          ((fun z : (X × X₁) × (Y × Y₁) => z.1.1) ∘ R) ; Pi] =
          H[fun w : (X × Y₁) × (X₁ × Y) => (w.1.1, w.2.1) ; Pi] :=
        entropyRV_eq_of_injective _ (fun t : X × X₁ => (t.2, t.1))
          (fun a b he => Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)) fun _ => rfl
      have i₂ : H[(fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R ; Pi] =
          H[fun w : (X × Y₁) × (X₁ × Y) => ((), w.2.1) ; Pi] :=
        (entropyRV_eq_of_injective _ (fun t : X₁ => ((), t))
          (fun a b he => congrArg Prod.snd he) fun _ => rfl).symm
      have i₃ : H[pair (pair ((fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R)
          ((fun z : (X × X₁) × (Y × Y₁) => z.2.2) ∘ R))
          ((fun z : (X × X₁) × (Y × Y₁) => z.1.1) ∘ R) ; Pi] =
          H[fun w : (X × Y₁) × (X₁ × Y) => (w.1, w.2.1) ; Pi] :=
        entropyRV_eq_of_injective _ (fun t : (X × Y₁) × X₁ => ((t.2, t.1.2), t.1.1))
          (fun a b he => by
            have h₁ := congrArg (fun t => t.1.1) he
            have h₂ := congrArg (fun t => t.1.2) he
            have h₃ := congrArg Prod.snd he
            exact Prod.ext (Prod.ext h₃ h₂) h₁) fun _ => rfl
      have i₄ : H[pair ((fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R)
          ((fun z : (X × X₁) × (Y × Y₁) => z.2.2) ∘ R) ; Pi] =
          H[fun w : (X × Y₁) × (X₁ × Y) => (w.1.2, w.2.1) ; Pi] :=
        entropyRV_eq_of_injective _ (fun t : Y₁ × X₁ => (t.2, t.1))
          (fun a b he => Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)) fun _ => rfl
      have hent : H[pair (Prod.fst : X × Y₁ → X) Prod.snd ; jointOf q₁ κ₁] =
          H[fun t : X × Y₁ => t ; jointOf q₁ κ₁] := rfl
      have hgoal : H[pair ((fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R)
          ((fun z : (X × X₁) × (Y × Y₁) => z.1.1) ∘ R) ; Pi] -
          H[(fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R ; Pi] -
          H[pair (pair ((fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R)
            ((fun z : (X × X₁) × (Y × Y₁) => z.2.2) ∘ R))
            ((fun z : (X × X₁) × (Y × Y₁) => z.1.1) ∘ R) ; Pi] +
          H[pair ((fun z : (X × X₁) × (Y × Y₁) => z.1.2) ∘ R)
            ((fun z : (X × X₁) × (Y × Y₁) => z.2.2) ∘ R) ; Pi] =
          H[Prod.fst ; jointOf q₁ κ₁] + H[Prod.snd ; jointOf q₁ κ₁] -
            H[pair Prod.fst Prod.snd ; jointOf q₁ κ₁] := by
        rw [i₁, i₂, i₃, i₄, e₁, e₂, e₃, e₄, z₁, hent]
        have hf : H[fun t : X × Y₁ => t.1 ; jointOf q₁ κ₁] = H[Prod.fst ; jointOf q₁ κ₁] := rfl
        have hs : H[fun t : X × Y₁ => t.2 ; jointOf q₁ κ₁] = H[Prod.snd ; jointOf q₁ κ₁] := rfl
        rw [hf, hs]
        ring
      exact hgoal
    exact isAchievableRC_multihop hp hW
      (by rw [hIy]; exact hR.trans_le (min_le_left _ _))
      (by rw [hDf]; exact hR.trans_le (min_le_right _ _))
  · refine (hR.le_rcCutsetBound hW).trans (csSup_le ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩ ?_)
    rintro _ ⟨q, hq, rfl⟩
    refine min_le_min ?_ ?_
    · have e : bcMarg₁ W = κ₂ ∘ Prod.snd := funext hm₁
      rw [rcMacInfo, e, mutualInfoOf_comp hq h₂]
      exact mutualInfoOf_le_capacity (hq.dist _) h₂
    · have hJ := jointOf_isPMF hq hW
      rw [rcBcInfo_degraded hdeg hq hW, rcDfInfo, condMutualInfo_comm hJ, condMutualInfo_eq' hJ]
      have hle := condEntropy_le_entropy hJ (fun z : (X × X₁) × (Y × Y₁) => z.2.2)
        (fun z : (X × X₁) × (Y × Y₁) => z.1.2)
      let Sw : X × X₁ → X₁ × X := fun a => (a.2, a.1)
      have hSw : Function.Injective Sw := fun a b he =>
        Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
      have hA : ∀ a, dist (jointOf q W) (pair (fun z => z.1.2) fun z => z.1.1) (Sw a) = q a := by
        intro a
        have := dist_comp_of_injective (jointOf q W) Prod.fst hSw a
        rw [dist_jointOf_fst hW] at this
        exact this
      have hmarg : ∀ a y₁, dist (jointOf q W) (fun z => (z.1, z.2.2)) (a, y₁) =
          q a * κ₁ a.1 y₁ := by
        intro a y₁
        have h₀ := dist_pair_marg_fst (jointOf q W) Prod.fst
          (fun z : (X × X₁) × (Y × Y₁) => (z.2.2, z.2.1)) a y₁
        have h₃ : ∀ y, dist (jointOf q W) (pair Prod.fst fun z => (z.2.2, z.2.1)) (a, (y₁, y)) =
            jointOf q W (a, (y, y₁)) := by
          intro y
          have hinj : Function.Injective fun z : (X × X₁) × (Y × Y₁) => (z.1, (z.2.2, z.2.1)) :=
            fun u v he => by
              have h₁ := congrArg Prod.fst he
              have h₂ := congrArg (fun t => t.2.1) he
              have h₃ := congrArg (fun t => t.2.2) he
              exact Prod.ext h₁ (Prod.ext h₃ h₂)
          have := dist_comp_of_injective (jointOf q W) id hinj (a, (y, y₁))
          rw [dist_id] at this
          exact this
        have e₁ : dist (jointOf q W) (fun z => (z.1, z.2.2)) (a, y₁) =
            dist (jointOf q W) (pair Prod.fst fun z => (z.2.2, z.2.1).1) (a, y₁) := rfl
        rw [e₁, h₀]
        simp_rw [h₃]
        simp only [jointOf, ← mul_sum]
        have := congrFun (hm₂ a) y₁
        simp only [bcMarg₂] at this
        rw [this]
      have hchan : ∀ (t : X₁ × X) (y₁ : Y₁), dist (jointOf q W)
          (pair (pair (fun z => z.1.2) fun z => z.1.1) fun z => z.2.2) (t, y₁) =
          dist (jointOf q W) (pair (fun z => z.1.2) fun z => z.1.1) t * κ₁ t.2 y₁ := by
        rintro ⟨s, x⟩ y₁
        have hA' := hA (x, s)
        have hperm : Function.Injective fun t : (X × X₁) × Y₁ => ((t.1.2, t.1.1), t.2) :=
          fun u v he => by
            have h₁ := congrArg (fun t => t.1.1) he
            have h₂ := congrArg (fun t => t.1.2) he
            have h₃ := congrArg Prod.snd he
            exact Prod.ext (Prod.ext h₂ h₁) h₃
        have h₄ := dist_comp_of_injective (jointOf q W) (fun z => (z.1, z.2.2)) hperm ((x, s), y₁)
        have e₂ : dist (jointOf q W) (pair (pair (fun z => z.1.2) fun z => z.1.1) fun z => z.2.2)
            ((s, x), y₁) = dist (jointOf q W) (fun z => (z.1, z.2.2)) ((x, s), y₁) := h₄
        have e₃ : dist (jointOf q W) (pair (fun z => z.1.2) fun z => z.1.1) (s, x) = q (x, s) := hA'
        rw [e₂, e₃, hmarg]
      have hI := entropy_sub_condEntropy_eq_mutualInfoOf (fun t : X₁ × X => t.2) hJ h₁ hchan
      have hcap := mutualInfoOf_le_capacity (hJ.dist ((fun t : X₁ × X => t.2) ∘
        pair (fun z : (X × X₁) × (Y × Y₁) => z.1.2) fun z => z.1.1)) h₁
      linarith

end Cascade

end InfoTheory
