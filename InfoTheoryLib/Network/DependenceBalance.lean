/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.ICStrong
public import InfoTheoryLib.Network.TwoWayExamples

/-!
# The dependence balance outer bound

Theorem 6 on page 18-51 of the notes, for the two-way channel with a common output.

## Main definitions

* `twcDepRegion`: the dependence balance region.

## Main statements

* `condMutualInfo_interaction`: `I(A; B | C, O) - I(A; B | C) = I(A; O | C, B) - I(A; O | C)`.
* `mix_condMutualInfo`: the conditional mutual information of a mixture, when the index of the
  mixture is known.
* `IsAchievableTWC.mem_closure_twcDepRegion`: **Theorem 6, the dependence balance outer bound**.

## Implementation notes

The notes identify `Uᵢ = Y^{i-1}` and leave the proof as an exercise. We use `U = (Q, Y^{Q-1})` with
a uniform time `Q`. The key step is
`I(M₁; M₂ | Yⁱ) - I(M₁; M₂ | Y^{i-1}) ≤ I(X₁ᵢ; X₂ᵢ | Yᵢ, Uᵢ) - I(X₁ᵢ; X₂ᵢ | Uᵢ)`, which telescopes.
We do not prove the bound `|U| ≤ 3`, so the alphabet of `U` is arbitrary in the region.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

/-! ### Identities -/

section Identities

variable {Ω a b c d : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  {μ : Ω → ℝ}

/-- **The symmetry of the interaction information.** -/
theorem condMutualInfo_interaction (hμ : IsPMF μ) (A : Ω → a) (B : Ω → b) (O : Ω → d) (C : Ω → c) :
    I[A : B | pair C O ; μ] - I[A : B | C ; μ] = I[A : O | pair C B ; μ] - I[A : O | C ; μ] := by
  have h₁ : H[pair (pair (pair C O) B) A ; μ] = H[pair (pair (pair C B) O) A ; μ] :=
    entropyRV_eq_of_injective μ (fun t : ((c × b) × d) × a => (((t.1.1.1, t.1.2), t.1.1.2), t.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc, and_left_comm, and_comm] using h)
      fun _ => rfl
  have h₂ : H[pair (pair C O) B ; μ] = H[pair (pair C B) O ; μ] :=
    entropyRV_eq_of_injective μ (fun t : (c × b) × d => ((t.1.1, t.2), t.1.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc, and_left_comm, and_comm] using h)
      fun _ => rfl
  rw [condMutualInfo_eq_entropies hμ, condMutualInfo_eq_entropies hμ,
    condMutualInfo_eq_entropies hμ, condMutualInfo_eq_entropies hμ, h₁, h₂]
  ring

/-- The conditional mutual information does not change when each of two conditioning variables is a
function of the other. -/
lemma condMutualInfo_cond_congr' (hμ : IsPMF μ) (X : Ω → a) (Y : Ω → b) {C : Ω → c} {C' : Ω → d}
    (f : c → d) (g : d → c) (h₁ : C' = f ∘ C) (h₂ : C = g ∘ C') :
    I[X : Y | C' ; μ] = I[X : Y | C ; μ] := by
  have key : ∀ {e : Type _} [Fintype e] (Z : Ω → e), H[Z | C' ; μ] = H[Z | C ; μ] := by
    intro e _ Z
    refine le_antisymm ?_ ?_
    · have := condEntropy_le_condEntropy_comp hμ Z C' g
      rwa [← h₂] at this
    · have := condEntropy_le_condEntropy_comp hμ Z C f
      rwa [← h₁] at this
  have key₂ : H[X | pair Y C' ; μ] = H[X | pair Y C ; μ] := by
    refine le_antisymm ?_ ?_
    · have := condEntropy_le_condEntropy_comp hμ X (pair Y C') (fun t : b × d => (t.1, g t.2))
      have e : (fun t : b × d => (t.1, g t.2)) ∘ pair Y C' = pair Y C := by
        rw [h₂]
        rfl
      rwa [e] at this
    · have := condEntropy_le_condEntropy_comp hμ X (pair Y C) (fun t : b × c => (t.1, f t.2))
      have e : (fun t : b × c => (t.1, f t.2)) ∘ pair Y C = pair Y C' := by
        rw [h₁]
        rfl
      rwa [e] at this
  simp only [condMutualInfo]
  rw [key, key₂]

variable {ι T : Type*} [Fintype ι] [Fintype T] {w : ι → ℝ} {ν : ι → T → ℝ}

omit [Fintype a] in
/-- The law of the index and of a function of the mixture. -/
lemma dist_mix (g : T → a) :
    dist (jointOf w ν) (fun z => (z.1, g z.2)) = jointOf w fun i => dist (ν i) g := by
  classical
  funext ⟨i, x⟩
  rw [dist_jointOf_row]
  rw [sum_eq_single i]
  · congr 1
    simp only [dist, Prod.mk.injEq, true_and]
  · intro j _ hj
    have : dist (ν j) (fun o => (j, g o)) (i, x) = 0 :=
      sum_eq_zero fun o _ => ite_eq_right fun h => absurd (Prod.ext_iff.mp h).1 hj
    rw [this, mul_zero]
  · simp

/-- The entropy of a mixture, when the index of the mixture is known. -/
lemma mix_entropy (hw : IsPMF w) (hν : ∀ i, IsPMF (ν i)) (g : T → a) :
    H[fun z => (z.1, g z.2) ; jointOf w ν] = entropy w + ∑ i, w i * H[g ; ν i] := by
  rw [entropyRV, dist_mix]
  exact entropy_jointOf hw fun i => (hν i).dist g

/-- **The conditional mutual information of a mixture**, when the index of the mixture is known. -/
theorem mix_condMutualInfo (hw : IsPMF w) (hν : ∀ i, IsPMF (ν i)) (A : T → a) (B : T → b)
    (C : T → c) :
    I[A ∘ Prod.snd : B ∘ Prod.snd | fun z => (z.1, C z.2) ; jointOf w ν] =
      ∑ i, w i * I[A : B | C ; ν i] := by
  have hM : IsPMF (jointOf w ν) := jointOf_isPMF hw hν
  have e₁ : H[pair (fun z : ι × T => (z.1, C z.2)) (A ∘ Prod.snd) ; jointOf w ν] =
      H[fun z => (z.1, pair C A z.2) ; jointOf w ν] :=
    entropyRV_eq_of_injective _ (fun t : ι × (c × a) => ((t.1, t.2.1), t.2.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc] using h) fun _ => rfl
  have e₂ : H[pair (fun z : ι × T => (z.1, C z.2)) (B ∘ Prod.snd) ; jointOf w ν] =
      H[fun z => (z.1, pair C B z.2) ; jointOf w ν] :=
    entropyRV_eq_of_injective _ (fun t : ι × (c × b) => ((t.1, t.2.1), t.2.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc] using h) fun _ => rfl
  have e₃ : H[pair (pair (fun z : ι × T => (z.1, C z.2)) (B ∘ Prod.snd)) (A ∘ Prod.snd) ;
      jointOf w ν] = H[fun z => (z.1, pair (pair C B) A z.2) ; jointOf w ν] :=
    entropyRV_eq_of_injective _ (fun t : ι × ((c × b) × a) => (((t.1, t.2.1.1), t.2.1.2), t.2.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc] using h) fun _ => rfl
  rw [condMutualInfo_eq_entropies hM, e₁, e₂, e₃, mix_entropy hw hν, mix_entropy hw hν,
    mix_entropy hw hν, mix_entropy hw hν]
  simp only [condMutualInfo_eq_entropies (hν _), mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
  ring

omit [Fintype d] in
/-- The informations of a law that is an arrangement of a mixture. -/
lemma mix_info_transfer {Ω' e e' : Type*} [Fintype Ω'] [Fintype e] [Fintype e'] (hw : IsPMF w)
    (hν : ∀ i, IsPMF (ν i)) {Φ : ι × T → Ω'} {L : Ω' → ℝ} (hL : L = dist (jointOf w ν) Φ)
    (A : Ω' → a) (B : Ω' → b) (C : Ω' → e) (A' : T → a) (B' : T → b) (C' : T → e')
    (f : ι × e' → e) (hf : Function.Injective f) (hA : A ∘ Φ = A' ∘ Prod.snd)
    (hB : B ∘ Φ = B' ∘ Prod.snd) (hC : C ∘ Φ = f ∘ fun z => (z.1, C' z.2)) :
    I[A : B | C ; L] = ∑ i, w i * I[A' : B' | C' ; ν i] := by
  have hM : IsPMF (jointOf w ν) := jointOf_isPMF hw hν
  rw [hL, condMutualInfo_dist hM, hA, hB, hC]
  exact (condMutualInfo_cond_congr hM _ _ (C := fun z : ι × T => (z.1, C' z.2)) f hf
    fun _ => rfl).trans (mix_condMutualInfo hw hν A' B' C')

end Identities

/-! ### One code -/

section Code

variable {X₁ X₂ : Type*} {Y : Type u} [Fintype X₁] [Fintype X₂] [Fintype Y]
  {V : X₁ × X₂ → Y → ℝ} {M₁ M₂ n : ℕ}

/-- The dependence balance region: `R₁ ≤ I(X₁; Y | X₂, U)`, `R₂ ≤ I(X₂; Y | X₁, U)` and
`I(X₁; X₂ | U) ≤ I(X₁; X₂ | Y, U)`, in bits, for some `p(u, x₁, x₂)` with a finite `U`. -/
def twcDepRegion (V : X₁ × X₂ → Y → ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (U : Type u) (_ : Fintype U) (p : U × (X₁ × X₂) → ℝ), IsPMF p ∧
    R.1 ≤ I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ;
      jointOf p fun t => V t.2] / log 2 ∧
    R.2 ≤ I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ;
      jointOf p fun t => V t.2] / log 2 ∧
    I[fun z => z.1.2.1 : fun z => z.1.2.2 | fun z => z.1.1 ; jointOf p fun t => V t.2] ≤
      I[fun z => z.1.2.1 : fun z => z.1.2.2 | fun z => (z.1.1, z.2) ; jointOf p fun t => V t.2]}

namespace TWCCode

variable (c : TWCCode M₁ M₂ n X₁ X₂ Y Y)

/-- The law of the messages and of the outputs. -/
abbrev dLaw (V : X₁ × X₂ → Y → ℝ) : (Fin M₁ × Fin M₂) × (Fin n → Y) → ℝ := c.law V id id

/-- The past `Y^{i-1}`, with an alphabet that does not depend on `i`. -/
abbrev dC (i : Fin n) (z : (Fin M₁ × Fin M₂) × (Fin n → Y)) : Fin n → Option Y :=
  degradedBCPast (i : ℕ) z.2

/-- The inputs at time `i`. -/
def dX (i : Fin n) (z : (Fin M₁ × Fin M₂) × (Fin n → Y)) : X₁ × X₂ :=
  c.fbEnc id id i z.1 (fbPre i z.2)

/-- The output at time `i`. -/
abbrev dO (i : Fin n) (z : (Fin M₁ × Fin M₂) × (Fin n → Y)) : Y := z.2 i

/-- The first input at time `i`. -/
abbrev dX₁ (i : Fin n) (z : (Fin M₁ × Fin M₂) × (Fin n → Y)) : X₁ := (c.dX i z).1

/-- The second input at time `i`. -/
abbrev dX₂ (i : Fin n) (z : (Fin M₁ × Fin M₂) × (Fin n → Y)) : X₂ := (c.dX i z).2

/-- The letter at time `i`. -/
def dR (i : Fin n) (z : (Fin M₁ × Fin M₂) × (Fin n → Y)) :
    ((Fin n → Option Y) × (X₁ × X₂)) × Y :=
  ((dC i z, c.dX i z), dO i z)

variable [Nonempty (Fin M₁ × Fin M₂)]

omit [Fintype X₁] [Fintype X₂] in
lemma dLaw_isPMF (hV : IsChannel V) : IsPMF (c.dLaw V) := fbLaw_isPMF uniformPMF_isPMF hV n

omit [Nonempty (Fin M₁ × Fin M₂)] in
/-- `H(Yᵢ | Yⁱ⁻¹, Xᵢ) = ∑ p(x) H(V x)`. -/
lemma condEntropy_dX (hV : IsChannel V) (i : Fin n) :
    H[dO i | pair (dC i) (c.dX i) ; c.dLaw V] =
      ∑ a, dist (c.dLaw V) (c.dX i) a * entropy (V a) := by
  classical
  have hd : dist (c.dLaw V) (c.dX i) = dist (c.dLaw V) (Prod.snd ∘ pair (dC i) (c.dX i)) := rfl
  rw [hd]
  refine condEntropy_of_channel (W := V) Prod.snd fun t b => ?_
  have h := dist_fbLaw_letter (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := V)
    (enc := c.fbEnc id id) hV i
    (fun t : (Fin M₁ × Fin M₂) × (Fin i → Y) => (BCFBCode.mask i t.2, c.fbEnc id id i t.1 t.2))
    Prod.snd (fun _ _ => rfl) t b
  simp only [BCFBCode.mask_fbPre] at h
  exact h

/-- `H(Yᵢ | Yⁱ⁻¹, M₁, M₂) = ∑ p(x) H(V x)`. -/
lemma condEntropy_dM (hV : IsChannel V) (i : Fin n) :
    H[dO i | pair (dC i) Prod.fst ; c.dLaw V] =
      ∑ a, dist (c.dLaw V) (c.dX i) a * entropy (V a) := by
  classical
  have hμ := c.dLaw_isPMF hV
  have hinj : H[dO i | pair (dC i) Prod.fst ; c.dLaw V] =
      H[dO i | pair (fun z => fbPre i z.2) Prod.fst ; c.dLaw V] :=
    condEntropy_congr_right hμ _ (fun t : (Fin i → Y) × (Fin M₁ × Fin M₂) =>
      (BCFBCode.mask i t.1, t.2))
      (fun a b h => Prod.ext (BCFBCode.mask_injective i (Prod.ext_iff.mp h).1)
        (Prod.ext_iff.mp h).2)
      fun z => by simp only [pair, BCFBCode.mask_fbPre]
  have hd : dist (c.dLaw V) (c.dX i) = dist (c.dLaw V)
      ((fun t : (Fin i → Y) × (Fin M₁ × Fin M₂) => c.fbEnc id id i t.2 t.1) ∘
        pair (fun z => fbPre i z.2) Prod.fst) := rfl
  rw [hinj, hd]
  refine condEntropy_of_channel (W := V) _ fun t b => ?_
  exact dist_fbLaw_letter (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := V)
    (enc := c.fbEnc id id) hV i
    (fun t : (Fin M₁ × Fin M₂) × (Fin i → Y) => (t.2, t.1))
    (fun t => c.fbEnc id id i t.2 t.1) (fun _ _ => rfl) t b

omit [Fintype X₁] [Fintype X₂] in
/-- Conditioning on a message gives less entropy than conditioning on the input that it determines,
given the past. -/
lemma condEntropy_msg_le (hV : IsChannel V) (i : Fin n) {B γ : Type*} [Fintype B] [Fintype γ]
    (mb : Fin M₁ × Fin M₂ → B) (φ : (Fin M₁ × Fin M₂) × (Fin n → Y) → γ)
    (e : B → (Fin i → Y) → γ) (he : ∀ z, φ z = e (mb z.1) (fbPre i z.2)) :
    H[dO i | pair (dC i) (fun z => mb z.1) ; c.dLaw V] ≤ H[dO i | pair (dC i) φ ; c.dLaw V] := by
  have hμ := c.dLaw_isPMF hV
  have hinj : H[dO i | pair (dC i) (fun z => mb z.1) ; c.dLaw V] =
      H[dO i | pair (fun z => fbPre i z.2) (fun z => mb z.1) ; c.dLaw V] :=
    condEntropy_congr_right hμ _ (fun t : (Fin i → Y) × B => (BCFBCode.mask i t.1, t.2))
      (fun a b h => Prod.ext (BCFBCode.mask_injective i (Prod.ext_iff.mp h).1)
        (Prod.ext_iff.mp h).2)
      fun z => by simp only [pair, BCFBCode.mask_fbPre]
  rw [hinj]
  have h := condEntropy_le_condEntropy_comp hμ (dO i)
    (pair (fun z => fbPre i z.2) fun z => mb z.1)
    (fun t : (Fin i → Y) × B => (BCFBCode.mask i t.1, e t.2 t.1))
  have e' : (fun t : (Fin i → Y) × B => (BCFBCode.mask i t.1, e t.2 t.1)) ∘
      pair (fun z => fbPre i z.2) (fun z => mb z.1) = pair (dC i) φ := by
    funext z
    simp only [Function.comp, pair, he, BCFBCode.mask_fbPre]
  rwa [e'] at h

omit [Fintype X₁] [Fintype X₂] in
/-- The past `Yⁱ` from `Y^{i-1}` and `Yᵢ`, and conversely. -/
lemma condMutualInfo_past_succ [Nonempty Y] (hV : IsChannel V) (i : Fin n) {a b : Type*} [Fintype a]
    [Fintype b] (A : (Fin M₁ × Fin M₂) × (Fin n → Y) → a)
    (B : (Fin M₁ × Fin M₂) × (Fin n → Y) → b) :
    I[A : B | fun z => degradedBCPast ((i : ℕ) + 1) z.2 ; c.dLaw V] =
      I[A : B | pair (dC i) (dO i) ; c.dLaw V] := by
  classical
  refine condMutualInfo_cond_congr' (c.dLaw_isPMF hV) A B
    (fun t : (Fin n → Option Y) × Y => Function.update t.1 i (some t.2))
    (fun p : Fin n → Option Y => (Function.update p i none, (p i).getD (Classical.arbitrary Y)))
    ?_ ?_
  · funext z
    funext j
    simp only [Function.comp, pair, degradedBCPast, Function.update_apply]
    by_cases hj : j = i
    · subst hj
      simp
    · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      have : ((j : ℕ) < i + 1) ↔ (j : ℕ) < i := by omega
      simp [hj, this]
  · funext z
    refine Prod.ext ?_ ?_
    · funext j
      simp only [Function.comp, degradedBCPast, Function.update_apply]
      by_cases hj : j = i
      · subst hj
        simp [dC, degradedBCPast]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        have : ((j : ℕ) < i + 1) ↔ (j : ℕ) < i := by omega
        simp [hj, this, dC, degradedBCPast]
    · simp [Function.comp, degradedBCPast]

/-- **The key inequality.** -/
theorem depBalance_step [Nonempty Y] (hV : IsChannel V) (i : Fin n) :
    I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : fun z => z.1.2 |
        fun z => degradedBCPast ((i : ℕ) + 1) z.2 ; c.dLaw V] -
      I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : fun z => z.1.2 |
        fun z => degradedBCPast (i : ℕ) z.2 ; c.dLaw V] ≤
    I[c.dX₁ i : c.dX₂ i | pair (dC i) (dO i) ; c.dLaw V] -
      I[c.dX₁ i : c.dX₂ i | dC i ; c.dLaw V] := by
  classical
  have hμ := c.dLaw_isPMF hV
  rw [condMutualInfo_past_succ c hV]
  rw [condMutualInfo_interaction hμ (fun z => z.1.1) (fun z => z.1.2) (dO i) (dC i),
    condMutualInfo_interaction hμ (c.dX₁ i) (c.dX₂ i) (dO i) (dC i)]
  -- both sides as entropies of the output
  have hL : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : dO i |
      pair (dC i) (fun z => z.1.2) ; c.dLaw V] =
      H[dO i | pair (dC i) (fun z => z.1.2) ; c.dLaw V] -
        H[dO i | pair (dC i) Prod.fst ; c.dLaw V] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    congr 1
    exact condEntropy_congr_right hμ _ (fun t : (Fin n → Option Y) × (Fin M₁ × Fin M₂) =>
      ((t.1, t.2.2), t.2.1)) (fun s t h => by
        simpa [Prod.ext_iff, and_assoc, and_left_comm, and_comm] using h) fun _ => rfl
  have hL₀ : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : dO i | dC i ; c.dLaw V] =
      H[dO i | dC i ; c.dLaw V] - H[dO i | pair (dC i) (fun z => z.1.1) ; c.dLaw V] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
  have hR : I[c.dX₁ i : dO i | pair (dC i) (c.dX₂ i) ; c.dLaw V] =
      H[dO i | pair (dC i) (c.dX₂ i) ; c.dLaw V] - H[dO i | pair (dC i) (c.dX i) ; c.dLaw V] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    congr 1
    exact condEntropy_congr_right hμ _ (fun t : (Fin n → Option Y) × (X₁ × X₂) =>
      ((t.1, t.2.2), t.2.1)) (fun s t h => by
        simpa [Prod.ext_iff, and_assoc, and_left_comm, and_comm] using h) fun _ => rfl
  have hR₀ : I[c.dX₁ i : dO i | dC i ; c.dLaw V] =
      H[dO i | dC i ; c.dLaw V] - H[dO i | pair (dC i) (c.dX₁ i) ; c.dLaw V] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
  rw [hL, hL₀, hR, hR₀, c.condEntropy_dM hV, c.condEntropy_dX hV]
  have h₂ := c.condEntropy_msg_le hV i (fun w => w.2) (c.dX₂ i)
    (fun b u => c.enc₂ i b fun t => id (u t)) fun _ => rfl
  have h₁ := c.condEntropy_msg_le hV i (fun w => w.1) (c.dX₁ i)
    (fun b u => c.enc₁ i b fun t => id (u t)) fun _ => rfl
  linarith

omit [Fintype X₁] [Fintype X₂] in
/-- The messages are independent at the start. -/
lemma depBalance_zero [NeZero M₁] [NeZero M₂] (hV : IsChannel V) :
    I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : fun z => z.1.2 |
      fun z => degradedBCPast 0 z.2 ; c.dLaw V] = 0 := by
  classical
  have hμ := c.dLaw_isPMF hV
  have h₁ : 0 < M₁ := NeZero.pos _
  have h₂ : 0 < M₂ := NeZero.pos _
  have hM₁ : (M₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hM₂ : (M₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  have hd : dist (c.dLaw V) Prod.fst = uniformPMF (Fin M₁ × Fin M₂) := dist_fst_fbLaw hV n
  -- the conditioning is a constant
  have hC : (fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => degradedBCPast 0 z.2) =
      fun _ => fun _ => none := by
    funext z j
    simp [degradedBCPast]
  have e₁ : H[pair (fun _ : (Fin M₁ × Fin M₂) × (Fin n → Y) => (fun _ => none : Fin n → Option Y))
      (fun z => z.1.1) ; c.dLaw V] = H[fun z => z.1.1 ; c.dLaw V] :=
    entropyRV_eq_of_injective _ (fun a : Fin M₁ => ((fun _ => none : Fin n → Option Y), a))
      (fun s t h => (Prod.ext_iff.mp h).2) fun _ => rfl
  have e₂ : H[pair (fun _ : (Fin M₁ × Fin M₂) × (Fin n → Y) => (fun _ => none : Fin n → Option Y))
      (fun z => z.1.2) ; c.dLaw V] = H[fun z => z.1.2 ; c.dLaw V] :=
    entropyRV_eq_of_injective _ (fun a : Fin M₂ => ((fun _ => none : Fin n → Option Y), a))
      (fun s t h => (Prod.ext_iff.mp h).2) fun _ => rfl
  have e₃ : H[pair (pair (fun _ : (Fin M₁ × Fin M₂) × (Fin n → Y) =>
      (fun _ => none : Fin n → Option Y)) (fun z => z.1.2)) (fun z => z.1.1) ; c.dLaw V] =
      H[Prod.fst ; c.dLaw V] :=
    entropyRV_eq_of_injective _ (fun w : Fin M₁ × Fin M₂ =>
      (((fun _ => none : Fin n → Option Y), w.2), w.1))
      (fun s t h => by simpa [Prod.ext_iff, and_comm] using h) fun _ => rfl
  have e₄ : H[fun _ : (Fin M₁ × Fin M₂) × (Fin n → Y) => (fun _ => none : Fin n → Option Y) ;
      c.dLaw V] = 0 := by
    have hu : H[fun _ : (Fin M₁ × Fin M₂) × (Fin n → Y) => (fun _ => none : Fin n → Option Y) ;
        c.dLaw V] = H[fun _ : (Fin M₁ × Fin M₂) × (Fin n → Y) => () ; c.dLaw V] :=
      entropyRV_eq_of_injective _ (fun _ : Unit => (fun _ => none : Fin n → Option Y))
        (fun _ _ _ => rfl) fun _ => rfl
    have hc : dist (c.dLaw V) (fun _ => ()) = fun _ => 1 := by
      funext k
      simpa [dist] using hμ.sum_eq_one
    rw [hu, entropyRV, hc]
    simp [entropy]
  have hu₁ : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.1) = uniformPMF (Fin M₁) := by
    have := MACCode.dist_uniformPMF_prod_fst (M₁ := M₁) h₂ id
    rw [dist_id] at this
    exact this
  have hu₂ : (dist (uniformPMF (Fin M₁ × Fin M₂)) fun w => w.2) = uniformPMF (Fin M₂) := by
    have := MACCode.dist_uniformPMF_prod_snd (M₂ := M₂) h₁ id
    rw [dist_id] at this
    exact this
  have h₃ : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 ; c.dLaw V] = log M₁ := by
    have ee : (fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1) =
        (fun w : Fin M₁ × Fin M₂ => w.1) ∘ Prod.fst := rfl
    rw [entropyRV, ee, dist_comp_eq, hd, hu₁, entropy_uniformPMF, Fintype.card_fin]
  have h₄ : H[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.2 ; c.dLaw V] = log M₂ := by
    have ee : (fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.2) =
        (fun w : Fin M₁ × Fin M₂ => w.2) ∘ Prod.fst := rfl
    rw [entropyRV, ee, dist_comp_eq, hd, hu₂, entropy_uniformPMF, Fintype.card_fin]
  have h₅ : H[Prod.fst ; c.dLaw V] = log M₁ + log M₂ := by
    rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [log_mul hM₁ hM₂]
  rw [hC, condMutualInfo_eq_entropies hμ, e₁, e₂, e₃, e₄, h₃, h₄, h₅]
  ring

/-- `I(X₁; O | U, X₂)` at time `i`, as a difference of entropies of the output. -/
lemma info_dX₁ (hV : IsChannel V) (i : Fin n) :
    I[c.dX₁ i : dO i | pair (dC i) (c.dX₂ i) ; c.dLaw V] =
      H[dO i | pair (dC i) (c.dX₂ i) ; c.dLaw V] -
        ∑ a, dist (c.dLaw V) (c.dX i) a * entropy (V a) := by
  have hμ := c.dLaw_isPMF hV
  rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ, ← c.condEntropy_dX hV]
  congr 1
  exact condEntropy_congr_right hμ _ (fun t : (Fin n → Option Y) × (X₁ × X₂) =>
    ((t.1, t.2.2), t.2.1)) (fun s t h => by
      simpa [Prod.ext_iff, and_assoc, and_left_comm, and_comm] using h) fun _ => rfl

/-- `I(X₂; O | U, X₁)` at time `i`, as a difference of entropies of the output. -/
lemma info_dX₂ (hV : IsChannel V) (i : Fin n) :
    I[c.dX₂ i : dO i | pair (dC i) (c.dX₁ i) ; c.dLaw V] =
      H[dO i | pair (dC i) (c.dX₁ i) ; c.dLaw V] -
        ∑ a, dist (c.dLaw V) (c.dX i) a * entropy (V a) := by
  have hμ := c.dLaw_isPMF hV
  rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ, ← c.condEntropy_dX hV]
  congr 1
  exact condEntropy_congr_right hμ _ (fun t : (Fin n → Option Y) × (X₁ × X₂) =>
    ((t.1, t.2.1), t.2.2)) (fun s t h => by
      simpa [Prod.ext_iff, and_assoc] using h) fun _ => rfl

/-- `I(M₁; Yⁿ | M₂) ≤ ∑ᵢ I(X₁ᵢ; Yᵢ | X₂ᵢ, Uᵢ)`. -/
lemma condInfo₂_le (hV : IsChannel V) :
    I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : fun z i => id (z.2 i) |
      fun z => z.1.2 ; c.dLaw V] ≤
      ∑ i, I[c.dX₁ i : dO i | pair (dC i) (c.dX₂ i) ; c.dLaw V] := by
  have hμ := c.dLaw_isPMF hV
  have hI : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : fun z i => id (z.2 i) |
      fun z => z.1.2 ; c.dLaw V] = H[fun z i => id (z.2 i) | fun z => z.1.2 ; c.dLaw V] -
        H[fun z i => id (z.2 i) | Prod.fst ; c.dLaw V] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    congr 1
    exact condEntropy_congr_right hμ _ (fun w : Fin M₁ × Fin M₂ => (w.2, w.1))
      (fun a b h => Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1) fun _ => rfl
  rw [hI, condEntropy_eq_sum_past hμ, condEntropy_eq_sum_past hμ, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [c.info_dX₁ hV]
  have h₁ := c.condEntropy_msg_le hV i (fun w => w.2) (c.dX₂ i)
    (fun b u => c.enc₂ i b fun t => id (u t)) fun _ => rfl
  have h₂ := c.condEntropy_dM hV i
  have e₁ : H[fun ω : (Fin M₁ × Fin M₂) × (Fin n → Y) => id (ω.2 i) |
      pair (fun ω => degradedBCPast (i : ℕ) fun t => id (ω.2 t)) (fun z => z.1.2) ; c.dLaw V] =
      H[dO i | pair (dC i) (fun z => z.1.2) ; c.dLaw V] := rfl
  have e₂ : H[fun ω : (Fin M₁ × Fin M₂) × (Fin n → Y) => id (ω.2 i) |
      pair (fun ω => degradedBCPast (i : ℕ) fun t => id (ω.2 t)) Prod.fst ; c.dLaw V] =
      H[dO i | pair (dC i) Prod.fst ; c.dLaw V] := rfl
  rw [e₁, e₂]
  linarith

/-- `I(M₂; Yⁿ | M₁) ≤ ∑ᵢ I(X₂ᵢ; Yᵢ | X₁ᵢ, Uᵢ)`. -/
lemma condInfo₁_le (hV : IsChannel V) :
    I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.2 : fun z i => id (z.2 i) |
      fun z => z.1.1 ; c.dLaw V] ≤
      ∑ i, I[c.dX₂ i : dO i | pair (dC i) (c.dX₁ i) ; c.dLaw V] := by
  have hμ := c.dLaw_isPMF hV
  have hI : I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.2 : fun z i => id (z.2 i) |
      fun z => z.1.1 ; c.dLaw V] = H[fun z i => id (z.2 i) | fun z => z.1.1 ; c.dLaw V] -
        H[fun z i => id (z.2 i) | Prod.fst ; c.dLaw V] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
    rfl
  rw [hI, condEntropy_eq_sum_past hμ, condEntropy_eq_sum_past hμ, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [c.info_dX₂ hV]
  have h₁ := c.condEntropy_msg_le hV i (fun w => w.1) (c.dX₁ i)
    (fun b u => c.enc₁ i b fun t => id (u t)) fun _ => rfl
  have h₂ := c.condEntropy_dM hV i
  have e₁ : H[fun ω : (Fin M₁ × Fin M₂) × (Fin n → Y) => id (ω.2 i) |
      pair (fun ω => degradedBCPast (i : ℕ) fun t => id (ω.2 t)) (fun z => z.1.1) ; c.dLaw V] =
      H[dO i | pair (dC i) (fun z => z.1.1) ; c.dLaw V] := rfl
  have e₂ : H[fun ω : (Fin M₁ × Fin M₂) × (Fin n → Y) => id (ω.2 i) |
      pair (fun ω => degradedBCPast (i : ℕ) fun t => id (ω.2 t)) Prod.fst ; c.dLaw V] =
      H[dO i | pair (dC i) Prod.fst ; c.dLaw V] := rfl
  rw [e₁, e₂]
  linarith

/-- **The sum of the balance terms is nonnegative.** -/
theorem depBalance_sum [NeZero M₁] [NeZero M₂] [Nonempty Y] (hV : IsChannel V) :
    0 ≤ ∑ i, (I[c.dX₁ i : c.dX₂ i | pair (dC i) (dO i) ; c.dLaw V] -
      I[c.dX₁ i : c.dX₂ i | dC i ; c.dLaw V]) := by
  have hμ := c.dLaw_isPMF hV
  set J : ℕ → ℝ := fun k => I[fun z : (Fin M₁ × Fin M₂) × (Fin n → Y) => z.1.1 : fun z => z.1.2 |
    fun z => degradedBCPast k z.2 ; c.dLaw V] with hJ
  have hs : ∑ i : Fin n, (J ((i : ℕ) + 1) - J i) = J n - J 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => J (k + 1) - J k) n]
    exact sum_range_sub J n
  have h₀ : J 0 = 0 := c.depBalance_zero hV
  have hn : 0 ≤ J n := condMutualInfo_nonneg hμ _ _ _
  calc (0 : ℝ) ≤ J n - J 0 := by linarith
    _ = ∑ i : Fin n, (J ((i : ℕ) + 1) - J i) := hs.symm
    _ ≤ _ := sum_le_sum fun i _ => c.depBalance_step hV i

omit [Nonempty (Fin M₁ × Fin M₂)] in
/-- The law of the letter is memoryless. -/
lemma dist_dR (hV : IsChannel V) (i : Fin n) (t : ((Fin n → Option Y) × (X₁ × X₂)) × Y) :
    dist (c.dLaw V) (c.dR i) t = dist (dist (c.dLaw V) (c.dR i)) Prod.fst t.1 * V t.1.2 t.2 := by
  classical
  have h := dist_fbLaw_letter (ν := uniformPMF (Fin M₁ × Fin M₂)) (W := V)
    (enc := c.fbEnc id id) hV i
    (fun t : (Fin M₁ × Fin M₂) × (Fin i → Y) => (BCFBCode.mask i t.2, c.fbEnc id id i t.1 t.2))
    Prod.snd (fun _ _ => rfl) t.1 t.2
  simp only [BCFBCode.mask_fbPre] at h
  rw [← dist_comp_eq]
  exact h

end TWCCode

/-! ### The time sharing -/

section Mix

variable {M₁ M₂ n : ℕ} [NeZero M₁] [NeZero M₂] [Nonempty Y]

/-- The arrangement of a letter and of its time. -/
abbrev dΦ {n : ℕ} (z : Fin n × (((Fin n → Option Y) × (X₁ × X₂)) × Y)) :
    ((Fin n × (Fin n → Option Y)) × (X₁ × X₂)) × Y :=
  (((z.1, z.2.1.1), z.2.1.2), z.2.2)

/-- **The dependence balance bound for one code.** -/
theorem TWCCode.exists_dep (c : TWCCode M₁ M₂ n X₁ X₂ Y Y) (hV : IsChannel V) (hn : 0 < n) :
    ∃ (U : Type u) (_ : Fintype U) (p : U × (X₁ × X₂) → ℝ), IsPMF p ∧
      log M₁ ≤ n * I[fun z => z.1.2.1 : Prod.snd | fun z => (z.1.1, z.1.2.2) ;
        jointOf p fun t => V t.2] + log 2 + c.err₂ V id id * log M₁ ∧
      log M₂ ≤ n * I[fun z => z.1.2.2 : Prod.snd | fun z => (z.1.1, z.1.2.1) ;
        jointOf p fun t => V t.2] + log 2 + c.err₁ V id id * log M₂ ∧
      I[fun z => z.1.2.1 : fun z => z.1.2.2 | fun z => z.1.1 ; jointOf p fun t => V t.2] ≤
        I[fun z => z.1.2.1 : fun z => z.1.2.2 | fun z => (z.1.1, z.2) ; jointOf p fun t => V t.2] :=
          by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hM₁ : 0 < M₁ := NeZero.pos _
  have hM₂ : 0 < M₂ := NeZero.pos _
  have : Nonempty (Fin M₁ × Fin M₂) := ⟨(⟨0, hM₁⟩, ⟨0, hM₂⟩)⟩
  have hμ := c.dLaw_isPMF hV
  set μ := c.dLaw V with hμd
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set w : Fin n → ℝ := uniformPMF (Fin n) with hw
  have hwP : IsPMF w := uniformPMF_isPMF
  have hwv : ∀ i, w i = 1 / n := fun i => by simp [hw, uniformPMF]
  let ν : Fin n → ((Fin n → Option Y) × (X₁ × X₂)) × Y → ℝ := fun i => dist μ (c.dR i)
  have hν : ∀ i, IsPMF (ν i) := fun i => hμ.dist _
  have hM := jointOf_isPMF hwP hν
  let p : (Fin n × (Fin n → Option Y)) × (X₁ × X₂) → ℝ := fun t =>
    w t.1.1 * dist (ν t.1.1) Prod.fst (t.1.2, t.2)
  have hΦ : Function.Injective
      (dΦ : Fin n × (((Fin n → Option Y) × (X₁ × X₂)) × Y) → _) := fun s t h => by
    simpa [dΦ, Prod.ext_iff, and_assoc] using h
  have hL : (jointOf p fun t => V t.2) = dist (jointOf w ν) dΦ := by
    funext ⟨⟨⟨i, u⟩, x⟩, y⟩
    have h := dist_comp_of_injective (jointOf w ν) id hΦ (i, ((u, x), y))
    rw [dist_id] at h
    refine Eq.trans ?_ h.symm
    simp only [jointOf, p]
    rw [mul_assoc]
    congr 1
    exact (c.dist_dR hV i ((u, x), y)).symm
  have hp : IsPMF p := by
    have hLP : IsPMF (jointOf p fun t => V t.2) := by
      rw [hL]
      exact hM.dist _
    have hd : dist (jointOf p fun t => V t.2) Prod.fst = p := dist_jointOf_fst fun _ => hV _
    rw [← hd]
    exact hLP.dist _
  have hsum : ∀ g : Fin n → ℝ, ∑ i, g i = n * ∑ i, w i * g i := by
    intro g
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hwv]
    field_simp
  refine ⟨Fin n × (Fin n → Option Y), inferInstance, p, hp, ?_, ?_, ?_⟩
  · have h := mix_info_transfer hwP hν hL (fun z => z.1.2.1) Prod.snd (fun z => (z.1.1, z.1.2.2))
      (fun t => t.1.2.1) Prod.snd (fun t => (t.1.1, t.1.2.2))
      (fun s : Fin n × ((Fin n → Option Y) × X₂) => ((s.1, s.2.1), s.2.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc] using h) rfl rfl rfl
    have hb := c.condInfo₂_le hV
    have hf := c.log_le_of_fano₂ (W := V) (v₁ := id) (v₂ := id) hV hM₁ hM₂
    rw [h, ← hsum]
    have e : ∀ i, I[fun t : ((Fin n → Option Y) × (X₁ × X₂)) × Y => t.1.2.1 : Prod.snd |
        fun t => (t.1.1, t.1.2.2) ; ν i] =
        I[c.dX₁ i : TWCCode.dO i | pair (TWCCode.dC i) (c.dX₂ i) ; c.dLaw V] := fun i =>
      condMutualInfo_dist hμ (c.dR i) _ _ _
    simp only [e]
    linarith
  · have h := mix_info_transfer hwP hν hL (fun z => z.1.2.2) Prod.snd (fun z => (z.1.1, z.1.2.1))
      (fun t => t.1.2.2) Prod.snd (fun t => (t.1.1, t.1.2.1))
      (fun s : Fin n × ((Fin n → Option Y) × X₁) => ((s.1, s.2.1), s.2.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc] using h) rfl rfl rfl
    have hb := c.condInfo₁_le hV
    have hf := c.log_le_of_fano₁ (W := V) (v₁ := id) (v₂ := id) hV hM₁ hM₂
    rw [h, ← hsum]
    have e : ∀ i, I[fun t : ((Fin n → Option Y) × (X₁ × X₂)) × Y => t.1.2.2 : Prod.snd |
        fun t => (t.1.1, t.1.2.1) ; ν i] =
        I[c.dX₂ i : TWCCode.dO i | pair (TWCCode.dC i) (c.dX₁ i) ; c.dLaw V] := fun i =>
      condMutualInfo_dist hμ (c.dR i) _ _ _
    simp only [e]
    linarith
  · have h₁ := mix_info_transfer hwP hν hL (fun z => z.1.2.1) (fun z => z.1.2.2) (fun z => z.1.1)
      (fun t => t.1.2.1) (fun t => t.1.2.2) (fun t => t.1.1)
      (fun s : Fin n × (Fin n → Option Y) => s) (fun _ _ h => h) rfl rfl rfl
    have h₂ := mix_info_transfer hwP hν hL (fun z => z.1.2.1) (fun z => z.1.2.2)
      (fun z => (z.1.1, z.2))
      (fun t => t.1.2.1) (fun t => t.1.2.2) (fun t => (t.1.1, t.2))
      (fun s : Fin n × ((Fin n → Option Y) × Y) => ((s.1, s.2.1), s.2.2))
      (fun s t h => by simpa [Prod.ext_iff, and_assoc] using h) rfl rfl rfl
    rw [h₁, h₂, ← sub_nonneg, ← sum_sub_distrib]
    have hb := c.depBalance_sum hV
    have e : ∀ i, w i * I[fun t : ((Fin n → Option Y) × (X₁ × X₂)) × Y => t.1.2.1 :
        fun t => t.1.2.2 | fun t => (t.1.1, t.2) ; ν i] -
        w i * I[fun t : ((Fin n → Option Y) × (X₁ × X₂)) × Y => t.1.2.1 : fun t => t.1.2.2 |
          fun t => t.1.1 ; ν i] =
        w i * (I[c.dX₁ i : c.dX₂ i | pair (TWCCode.dC i) (TWCCode.dO i) ; c.dLaw V] -
          I[c.dX₁ i : c.dX₂ i | TWCCode.dC i ; c.dLaw V]) := fun i => by
      rw [mul_sub]
      congr 2
      · exact condMutualInfo_dist hμ (c.dR i) _ _ _
      · exact condMutualInfo_dist hμ (c.dR i) _ _ _
    simp only [e]
    have hbb := (hsum fun i =>
      (I[c.dX₁ i : c.dX₂ i | pair (TWCCode.dC i) (TWCCode.dO i) ; c.dLaw V] -
          I[c.dX₁ i : c.dX₂ i | TWCCode.dC i ; c.dLaw V]))
    rw [hbb] at hb
    exact nonneg_of_mul_nonneg_right (by linarith) hn'

end Mix

/-! ### The theorem -/

section Theorem

variable {M₁ M₂ n : ℕ}

omit [Fintype X₁] [Fintype X₂] in
/-- The law of the two-way channel with a common output, in terms of the output of the channel. -/
lemma TWCCode.sum_commonTW (c : TWCCode M₁ M₂ n X₁ X₂ Y Y) [DecidableEq (Fin n → Y)]
    (F : (Fin M₁ × Fin M₂) → (Fin n → Y) → Prop) [∀ w y, Decidable (F w y)]
    (w : Fin M₁ × Fin M₂) :
    ∑ y, (if F w y then c.law V id id (w, y) else 0) =
      ∑ z : Fin n → Y × Y, if F w (fun i => (z i).1) ∧ (fun i => (z i).2) = fun i => (z i).1 then
        c.law (commonTW V) Prod.fst Prod.snd (w, z) else 0 := by
  classical
  refine Finset.sum_of_injOn (fun y k => (y k, y k)) ?_ (fun _ _ => mem_univ _) ?_ ?_
  · intro y _ y' _ h
    funext k
    exact congrArg Prod.fst (congrFun h k)
  · intro z _ hz
    refine ite_eq_right fun ⟨_, h₂⟩ => absurd ?_ hz
    refine ⟨fun k => (z k).1, by simp, ?_⟩
    funext k
    exact Prod.ext rfl (congrFun h₂ k).symm
  · intro y _
    have hl : c.law V id id (w, y) =
      c.law (commonTW V) Prod.fst Prod.snd (w, fun k => (y k, y k)) := by
      rw [TWCCode.law, TWCCode.law, fbLaw_eq_prod, fbLaw_eq_prod]
      congr 1
      refine prod_congr rfl fun k _ => ?_
      simp only [commonTW]
      rw [ind_of_pos trivial, mul_one]
      rfl
    simp [hl]

omit [Fintype X₁] [Fintype X₂] [Fintype Y] in
/-- A law of the two-way channel with a common output vanishes when the two outputs differ. -/
lemma TWCCode.law_commonTW_eq_zero (c : TWCCode M₁ M₂ n X₁ X₂ Y Y) {w : Fin M₁ × Fin M₂}
    {z : Fin n → Y × Y} (h : (fun i => (z i).2) ≠ fun i => (z i).1) :
    c.law (commonTW V) Prod.fst Prod.snd (w, z) = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp h
  rw [TWCCode.law, fbLaw_eq_prod]
  refine mul_eq_zero_of_right _ (prod_eq_zero (mem_univ k) ?_)
  simp only [commonTW]
  rw [ind_of_neg hk, mul_zero]

omit [Fintype X₁] [Fintype X₂] in
/-- The error of node 2 with a common output. -/
lemma TWCCode.err₂_commonTW (c : TWCCode M₁ M₂ n X₁ X₂ Y Y) :
    c.err₂ (commonTW V) Prod.fst Prod.snd = c.err₂ V id id := by
  classical
  simp only [TWCCode.err₂, InfoTheory.errProb]
  refine (Fintype.sum_prod_type _).trans ((sum_congr rfl fun w _ => ?_).trans
    (Fintype.sum_prod_type _).symm)
  have h := c.sum_commonTW (V := V) (fun w y => c.dec₂ w.2 y ≠ w.1) w
  refine Eq.trans ?_ (h.symm.trans (sum_congr rfl fun y _ => by congr!))
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : (fun i => (z i).2) = fun i => (z i).1
  · simp [hz]
  · rw [c.law_commonTW_eq_zero hz]
    simp [hz]

omit [Fintype X₁] [Fintype X₂] in
/-- The error of node 1 with a common output. -/
lemma TWCCode.err₁_commonTW (c : TWCCode M₁ M₂ n X₁ X₂ Y Y) :
    c.err₁ (commonTW V) Prod.fst Prod.snd = c.err₁ V id id := by
  classical
  simp only [TWCCode.err₁, InfoTheory.errProb]
  refine (Fintype.sum_prod_type _).trans ((sum_congr rfl fun w _ => ?_).trans
    (Fintype.sum_prod_type _).symm)
  have h := c.sum_commonTW (V := V) (fun w y => c.dec₁ w.1 y ≠ w.2) w
  refine Eq.trans ?_ (h.symm.trans (sum_congr rfl fun y _ => by congr!))
  refine sum_congr rfl fun z _ => ?_
  by_cases hz : (fun i => (z i).2) = fun i => (z i).1
  · simp [hz]
  · rw [c.law_commonTW_eq_zero hz]
    simp [hz]

/-- **Theorem 6 (dependence balance outer bound), page 18-51 of [elgamal2010].** -/
theorem IsAchievableTWC.mem_closure_twcDepRegion [Nonempty Y] (hV : IsChannel V) {R₁ R₂ : ℝ}
    (h : IsAchievableTWC (commonTW V) R₁ R₂) : (R₁, R₂) ∈ closure (twcDepRegion V) := by
  obtain ⟨c, hc⟩ := h
  set a₁ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₁⌉₊ with ha₁
  set a₂ : ℕ → ℕ := fun n => ⌈(n : ℝ) * R₂⌉₊ with ha₂
  set P : ℕ → ℝ := fun n => (c n).errProb (commonTW V) with hPdef
  set ε : ℕ → ℝ := fun n => (1 + P n * ((a₁ n : ℝ) + a₂ n)) / n with hεdef
  have hpos₁ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₁⌉₊ := fun n => by positivity
  have hpos₂ : ∀ n : ℕ, 0 < 2 ^ ⌈(n : ℝ) * R₂⌉₊ := fun n => by positivity
  have he₁ : ∀ n, 0 ≤ (c n).err₁ V id id := fun n =>
    errProb_nonneg ((c n).law_isPMF hV (hpos₁ n) (hpos₂ n)) _ _ _
  have he₂ : ∀ n, 0 ≤ (c n).err₂ V id id := fun n =>
    errProb_nonneg ((c n).law_isPMF hV (hpos₁ n) (hpos₂ n)) _ _ _
  have hPe : ∀ n, P n = (c n).err₁ V id id + (c n).err₂ V id id := fun n => by
    simp only [hPdef, TWCCode.errProb, TWCCode.err₁_commonTW, TWCCode.err₂_commonTW]
  have hP₁ : ∀ n, (c n).err₁ V id id ≤ P n := fun n => by
    rw [hPe]
    linarith [he₂ n]
  have hP₂ : ∀ n, (c n).err₂ V id id ≤ P n := fun n => by
    rw [hPe]
    linarith [he₁ n]
  have hP0 : ∀ n, 0 ≤ P n := fun n => (he₁ n).trans (hP₁ n)
  have hL := log_two_pos'
  have hmem : ∀ n : ℕ, 0 < n → (R₁ - ε n, R₂ - ε n) ∈ twcDepRegion V := by
    intro n hn
    obtain ⟨U, hU, p, hp, b₁, b₂, b₃⟩ := (c n).exists_dep hV hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨U, hU, p, hp, ?_, ?_, b₃⟩
    · have h₃ := degradedBC_rate_le (b := a₂ n) (R := R₁) hn (hP0 n) (hP₂ n)
        (by exact_mod_cast b₁)
      refine h₃.trans (le_of_eq ?_)
      field_simp
    · have h₃ := degradedBC_rate_le (b := a₁ n) (R := R₂) hn (hP0 n) (hP₁ n)
        (by exact_mod_cast b₂)
      have e : ε n = (1 + P n * ((a₂ n : ℝ) + a₁ n)) / n := by
        simp only [hεdef, add_comm]
      rw [e]
      refine h₃.trans (le_of_eq ?_)
      field_simp
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_rate_eps hc hP0
  have hlim : Tendsto (fun n => (R₁ - ε n, R₂ - ε n)) atTop (𝓝 (R₁, R₂)) := by
    have h1 : Tendsto (fun n => R₁ - ε n) atTop (𝓝 (R₁ - 0)) := tendsto_const_nhds.sub hε
    have h2 : Tendsto (fun n => R₂ - ε n) atTop (𝓝 (R₂ - 0)) := tendsto_const_nhds.sub hε
    rw [sub_zero] at h1 h2
    exact h1.prodMk_nhds h2
  exact mem_closure_of_tendsto hlim ((eventually_gt_atTop 0).mono hmem)

end Theorem

end Code

end InfoTheory
