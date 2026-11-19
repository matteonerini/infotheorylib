/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.ConvexHessian
public import InfoTheoryLib.Network.BCMarton
public import InfoTheoryLib.Network.CardinalityBound

/-!
# The perturbation method for the Marton sum rate

The maximum of `I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)` over `p(u₁, u₂)` and `x(u₁, u₂)` is attained with
`|𝒰₁|, |𝒰₂| ≤ |𝒳|`, as in Appendix C of El Gamal and Kim.

## Implementation notes

The notes perturb a maximizer `p` to `p (1 + ε φ(u₁))`, keeping `p(x)` fixed, and compute two
derivatives at `ε = 0`. We use a simpler argument, which needs neither derivatives nor a maximizer.
Along the perturbation, `H(Y₁)` and `H(Y₂)` are constant, `H(U₁, U₂) - H(U₁, Y₁)` is affine in `ε`,
and `H(U₂, Y₂)` is concave in `ε`, so the objective is convex in `ε`. At one of the two ends of the
interval of `ε`, the objective is at least its value at `ε = 0`, and a value of `U₁` has probability
zero. So every `(p, x)` can be replaced, and not only a maximizer.

## Main definitions

* `martonSum q x W`: `I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)`.
* `martonPhi q x T₁ T₂`: `H(Y₁) + H(Y₂) + H(U₁, U₂) - H(U₁, Y₁) - H(U₂, Y₂)`.

## Main statements

* `martonSum_eq_martonPhi`: the sum rate in terms of entropies.
* `martonPhi_le_mix`: **the convexity along a perturbation**.
* `exists_marton_card`: **the bound**: for every `(p, x)` there is `(p', x')` on
  `|𝒰₁|, |𝒰₂| = |𝒳|` with at least the same sum rate.
* `exists_isMax_martonSum`: the maximum over all alphabets exists and is attained with
  `|𝒰₁|, |𝒰₂| = |𝒳|`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β β₁ β₂ 𝒰₁ 𝒰₂ : Type*} [Fintype β₁] [Fintype β₂] [Fintype 𝒰₁] [Fintype 𝒰₂]

/-- `I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)`. -/
def martonSum (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α) (W : α → β₁ × β₂ → ℝ) : ℝ :=
  martonInfo₁ q x W + martonInfo₂ q x W - martonInfo₁₂ q

/-- The law of `Y`. -/
def mLawY (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α) (T : α → β → ℝ) : β → ℝ :=
  fun y => ∑ z, q z * T (x z) y

/-- The law of `(U₁, Y)`. -/
def mLaw₁ (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α) (T : α → β → ℝ) : 𝒰₁ × β → ℝ :=
  fun s => ∑ u₂, q (s.1, u₂) * T (x (s.1, u₂)) s.2

/-- The law of `(U₂, Y)`. -/
def mLaw₂ (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α) (T : α → β → ℝ) : 𝒰₂ × β → ℝ :=
  fun s => ∑ u₁, q (u₁, s.1) * T (x (u₁, s.1)) s.2

/-- `H(Y₁) + H(Y₂) + H(U₁, U₂) - H(U₁, Y₁) - H(U₂, Y₂)`. -/
def martonPhi (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α) (T₁ : α → β₁ → ℝ) (T₂ : α → β₂ → ℝ) : ℝ :=
  entropy (mLawY q x T₁) + entropy (mLawY q x T₂) + entropy q - entropy (mLaw₁ q x T₁) -
    entropy (mLaw₂ q x T₂)

variable {q : 𝒰₁ × 𝒰₂ → ℝ} {x : 𝒰₁ × 𝒰₂ → α}

/-- `I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂) = H(Y₁) + H(Y₂) + H(U₁, U₂) - H(U₁, Y₁) - H(U₂, Y₂)`. -/
theorem martonSum_eq_martonPhi (hq : IsPMF q) {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W) :
    martonSum q x W = martonPhi q x (bcMarg₁ W) (bcMarg₂ W) := by
  classical
  have hK₁ : IsChannel (martonK₁ x W) := fun z => hW.bcMarg₁ (x z)
  have hK₂ : IsChannel (martonK₂ x W) := fun z => hW.bcMarg₂ (x z)
  have hμ₁ := jointOf_isPMF hq hK₁
  have hμ₂ := jointOf_isPMF hq hK₂
  have dU₁ : ∀ (K : 𝒰₁ × 𝒰₂ → β₁ → ℝ), IsChannel K → H[fun w : (𝒰₁ × 𝒰₂) × β₁ => w.1.1 ;
      jointOf q K] = H[Prod.fst ; q] := fun K hK => by
    have e : (fun w : (𝒰₁ × 𝒰₂) × β₁ => w.1.1) = Prod.fst ∘ Prod.fst := rfl
    rw [entropyRV, e, dist_comp_eq, dist_jointOf_fst hK]
    rfl
  have dU₂ : ∀ (K : 𝒰₁ × 𝒰₂ → β₂ → ℝ), IsChannel K → H[fun w : (𝒰₁ × 𝒰₂) × β₂ => w.1.2 ;
      jointOf q K] = H[Prod.snd ; q] := fun K hK => by
    have e : (fun w : (𝒰₁ × 𝒰₂) × β₂ => w.1.2) = Prod.snd ∘ Prod.fst := rfl
    rw [entropyRV, e, dist_comp_eq, dist_jointOf_fst hK]
    rfl
  have i₁ : martonInfo₁ q x W = entropy (mLawY q x (bcMarg₁ W)) -
      (entropy (mLaw₁ q x (bcMarg₁ W)) - H[Prod.fst ; q]) := by
    rw [martonInfo₁, mutualInfo_eq_entropy_sub_condEntropy' hμ₁, condEntropy_eq_sub hμ₁, dU₁ _ hK₁]
    congr 2
    · rw [entropyRV, dist_jointOf_snd]
      rfl
    · rw [entropyRV]
      congr 1
      funext s
      obtain ⟨u, y⟩ := s
      simp only [dist, pair_apply, Prod.mk.injEq, jointOf, Fintype.sum_prod_type, mLaw₁, martonK₁]
      rw [sum_eq_single u (fun u' _ hu => by simp [hu]) (by simp)]
      simp
  have i₂ : martonInfo₂ q x W = entropy (mLawY q x (bcMarg₂ W)) -
      (entropy (mLaw₂ q x (bcMarg₂ W)) - H[Prod.snd ; q]) := by
    rw [martonInfo₂, mutualInfo_eq_entropy_sub_condEntropy' hμ₂, condEntropy_eq_sub hμ₂, dU₂ _ hK₂]
    congr 2
    · rw [entropyRV, dist_jointOf_snd]
      rfl
    · rw [entropyRV]
      congr 1
      funext s
      obtain ⟨u, y⟩ := s
      simp only [dist, pair_apply, Prod.mk.injEq, jointOf, Fintype.sum_prod_type, mLaw₂, martonK₂]
      refine sum_congr rfl fun u₁ _ => ?_
      rw [sum_eq_single u (fun u' _ hu => by simp [hu]) (by simp)]
      simp
  have i₁₂ : martonInfo₁₂ q = H[Prod.snd ; q] - (entropy q - H[Prod.fst ; q]) := by
    have e : H[pair Prod.fst Prod.snd ; q] = entropy q := by rw [entropyRV, dist_pair_fst_snd]
    rw [martonInfo₁₂, mutualInfo_eq_entropy_sub_condEntropy' hq, condEntropy_eq_sub hq, e]
  rw [martonSum, i₁, i₂, i₁₂, martonPhi]
  ring

/-! ### Convexity along a perturbation -/

/-- The law `p(u₁, u₂) c(u₁)`. -/
def mPert (q : 𝒰₁ × 𝒰₂ → ℝ) (c : 𝒰₁ → ℝ) : 𝒰₁ × 𝒰₂ → ℝ := fun z => q z * c z.1

/-- If the law of `X` is fixed, so is the law of `Y`. -/
lemma mLawY_mPert [Finite α] {c : 𝒰₁ → ℝ} (h : dist (mPert q c) x = dist q x) (T : α → β → ℝ) :
    mLawY (mPert q c) x T = mLawY q x T := by
  have := Fintype.ofFinite α
  funext y
  have e := fun f : 𝒰₁ × 𝒰₂ → ℝ => sum_dist_mul f x fun a => T a y
  simp only [mLawY]
  rw [← e (mPert q c), h, e q]

/-- The entropy of the perturbed pair is `∑ c H + ∑ p(u₁) (-c log c)`. -/
lemma entropy_mPert (c : 𝒰₁ → ℝ) :
    entropy (mPert q c) = ∑ z, c z.1 * negMulLog (q z) + ∑ z, q z * negMulLog (c z.1) := by
  rw [entropy_eq_sum_negMulLog, ← sum_add_distrib]
  exact sum_congr rfl fun z _ => negMulLog_mul _ _

/-- The entropy of the perturbed `(U₁, Y)`. -/
lemma entropy_mLaw₁_mPert [Fintype β] {T : α → β → ℝ} (hT : IsChannel T) (c : 𝒰₁ → ℝ) :
    entropy (mLaw₁ (mPert q c) x T) = ∑ s, c s.1 * negMulLog (mLaw₁ q x T s) +
      ∑ z, q z * negMulLog (c z.1) := by
  have e : ∀ s, mLaw₁ (mPert q c) x T s = mLaw₁ q x T s * c s.1 := fun s => by
    simp only [mLaw₁, mPert, sum_mul]
    exact sum_congr rfl fun u₂ _ => by ring
  have e2 : ∑ s, mLaw₁ q x T s * negMulLog (c s.1) = ∑ z, q z * negMulLog (c z.1) := by
    simp only [Fintype.sum_prod_type (f := fun s : 𝒰₁ × β => mLaw₁ q x T s * negMulLog (c s.1)),
      Fintype.sum_prod_type (f := fun z : 𝒰₁ × 𝒰₂ => q z * negMulLog (c z.1)), ← sum_mul]
    refine sum_congr rfl fun u _ => ?_
    congr 1
    simp only [mLaw₁]
    rw [sum_comm]
    simp only [← mul_sum, (hT _).sum_eq_one, mul_one]
  rw [entropy_eq_sum_negMulLog, ← e2, ← sum_add_distrib]
  refine sum_congr rfl fun s _ => ?_
  rw [e, negMulLog_mul]

/-- **Convexity along a perturbation.** If `l c₁ + m c₂ = 1` and the perturbations keep the law of
`X`, then the objective at `p` is at most the mean of its values at `p c₁` and `p c₂`. -/
theorem martonPhi_le_mix [Finite α] (hq : ∀ z, 0 ≤ q z) {T₁ : α → β₁ → ℝ} {T₂ : α → β₂ → ℝ}
    (hT₁ : IsChannel T₁) (hT₂ : IsChannel T₂) {c₁ c₂ : 𝒰₁ → ℝ} (h₁ : ∀ u, 0 ≤ c₁ u)
    (h₂ : ∀ u, 0 ≤ c₂ u) {l m : ℝ} (hl : 0 ≤ l) (hm : 0 ≤ m) (hlm : l + m = 1)
    (hc : ∀ u, l * c₁ u + m * c₂ u = 1) (hx₁ : dist (mPert q c₁) x = dist q x)
    (hx₂ : dist (mPert q c₂) x = dist q x) :
    martonPhi q x T₁ T₂ ≤
      l * martonPhi (mPert q c₁) x T₁ T₂ + m * martonPhi (mPert q c₂) x T₁ T₂ := by
  -- The law of `(U₂, Y₂)` is the mixture of the perturbed laws.
  have hmix : mLaw₂ q x T₂ = l • mLaw₂ (mPert q c₁) x T₂ + m • mLaw₂ (mPert q c₂) x T₂ := by
    funext s
    simp only [mLaw₂, mPert, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    have := hc u
    calc q (u, s.1) * T₂ (x (u, s.1)) s.2
        = (l * c₁ u + m * c₂ u) * (q (u, s.1) * T₂ (x (u, s.1)) s.2) := by rw [this, one_mul]
      _ = _ := by ring
  have hnn : ∀ {c : 𝒰₁ → ℝ}, (∀ u, 0 ≤ c u) → ∀ s, 0 ≤ mLaw₂ (mPert q c) x T₂ s := fun hc s =>
    sum_nonneg fun u _ => mul_nonneg (mul_nonneg (hq _) (hc _)) ((hT₂ _).nonneg _)
  have hconc := (concaveOn_sum_negMulLog (ι := 𝒰₂ × β₂)).2 (x := mLaw₂ (mPert q c₁) x T₂)
    (y := mLaw₂ (mPert q c₂) x T₂) (hnn h₁) (hnn h₂) hl hm hlm
  have hH₂ : l * entropy (mLaw₂ (mPert q c₁) x T₂) + m * entropy (mLaw₂ (mPert q c₂) x T₂) ≤
      entropy (mLaw₂ q x T₂) := by
    rw [hmix]
    simpa only [entropy_eq_sum_negMulLog, smul_eq_mul] using hconc
  -- The affine part.
  have hA : l * (entropy (mPert q c₁) - entropy (mLaw₁ (mPert q c₁) x T₁)) +
      m * (entropy (mPert q c₂) - entropy (mLaw₁ (mPert q c₂) x T₁)) =
      entropy q - entropy (mLaw₁ q x T₁) := by
    rw [entropy_mPert, entropy_mPert, entropy_mLaw₁_mPert hT₁, entropy_mLaw₁_mPert hT₁,
      entropy_eq_sum_negMulLog q, entropy_eq_sum_negMulLog (mLaw₁ q x T₁)]
    have e1 : ∑ z, negMulLog (q z) = l * ∑ z, c₁ z.1 * negMulLog (q z) +
        m * ∑ z, c₂ z.1 * negMulLog (q z) := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun z _ => ?_
      have := hc z.1
      calc negMulLog (q z) = (l * c₁ z.1 + m * c₂ z.1) * negMulLog (q z) := by rw [this, one_mul]
        _ = _ := by ring
    have e2 : ∑ s, negMulLog (mLaw₁ q x T₁ s) = l * ∑ s, c₁ s.1 * negMulLog (mLaw₁ q x T₁ s) +
        m * ∑ s, c₂ s.1 * negMulLog (mLaw₁ q x T₁ s) := by
      simp only [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun s _ => ?_
      have := hc s.1
      calc negMulLog (mLaw₁ q x T₁ s)
          = (l * c₁ s.1 + m * c₂ s.1) * negMulLog (mLaw₁ q x T₁ s) := by rw [this, one_mul]
        _ = _ := by ring
    rw [e1, e2]
    ring
  simp only [martonPhi, mLawY_mPert hx₁, mLawY_mPert hx₂]
  have hlm' : m = 1 - l := by linarith
  subst hlm'
  nlinarith [hH₂, hA]

/-! ### Removing a value of `U₁` -/

/-- The law of `U₁`. -/
def mMarg₁ (q : 𝒰₁ × 𝒰₂ → ℝ) (u : 𝒰₁) : ℝ := ∑ v, q (u, v)

/-- The law of `U₂`. -/
def mMarg₂ (q : 𝒰₁ × 𝒰₂ → ℝ) (v : 𝒰₂) : ℝ := ∑ u, q (u, v)

open Classical in
/-- The support of `U₁`. -/
def mSupp₁ (q : 𝒰₁ × 𝒰₂ → ℝ) : Finset 𝒰₁ := univ.filter fun u => mMarg₁ q u ≠ 0

open Classical in
/-- The support of `U₂`. -/
def mSupp₂ (q : 𝒰₁ × 𝒰₂ → ℝ) : Finset 𝒰₂ := univ.filter fun v => mMarg₂ q v ≠ 0

lemma mem_mSupp₁ {u : 𝒰₁} : u ∈ mSupp₁ q ↔ mMarg₁ q u ≠ 0 := by simp [mSupp₁]

lemma mem_mSupp₂ {v : 𝒰₂} : v ∈ mSupp₂ q ↔ mMarg₂ q v ≠ 0 := by simp [mSupp₂]

lemma eq_zero_of_notMem_mSupp₁ (hq : ∀ z, 0 ≤ q z) {u : 𝒰₁} (hu : u ∉ mSupp₁ q) (v : 𝒰₂) :
    q (u, v) = 0 := by
  have h : mMarg₁ q u = 0 := by simpa [mem_mSupp₁] using hu
  exact (sum_eq_zero_iff_of_nonneg fun v _ => hq (u, v)).1 h v (mem_univ v)

lemma eq_zero_of_notMem_mSupp₂ (hq : ∀ z, 0 ≤ q z) {v : 𝒰₂} (hv : v ∉ mSupp₂ q) (u : 𝒰₁) :
    q (u, v) = 0 := by
  have h : mMarg₂ q v = 0 := by simpa [mem_mSupp₂] using hv
  exact (sum_eq_zero_iff_of_nonneg fun u _ => hq (u, v)).1 h u (mem_univ u)

/-- **Page C-9 of [elgamal2010].** If `|𝒰₁| > |𝒳|`, there is a nonzero `φ(u₁)` with
`E(φ(U₁) | X = x) = 0` for all `x`. -/
lemma exists_perturbation [Fintype α] (x : 𝒰₁ × 𝒰₂ → α)
    (hcard : Fintype.card α < (mSupp₁ q).card) :
    ∃ φ : 𝒰₁ → ℝ, (∀ u ∉ mSupp₁ q, φ u = 0) ∧ (∃ u ∈ mSupp₁ q, φ u ≠ 0) ∧
      dist (mPert q φ) x = 0 := by
  classical
  set S := mSupp₁ q with hS
  set M : Matrix α S ℝ := fun a s => dist (fun v : 𝒰₂ => q (s, v)) (fun v => x (s, v)) a with hM
  have hk : LinearMap.ker M.mulVecLin ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    simpa [Module.finrank_fintype_fun_eq_card] using hcard
  obtain ⟨φ₀, hφ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  obtain ⟨s, hs⟩ := Function.ne_iff.1 hne
  set φ : 𝒰₁ → ℝ := fun u => if h : u ∈ S then φ₀ ⟨u, h⟩ else 0 with hφ
  refine ⟨φ, fun u hu => by simp [hφ, hu], ⟨s, s.property, by simpa [hφ] using hs⟩, ?_⟩
  funext a
  have hz : (M.mulVec φ₀) a = 0 := by
    have := LinearMap.mem_ker.1 hφ₀
    exact congrFun this a
  have hsum : dist (mPert q φ) x a = (M.mulVec φ₀) a := by
    simp only [Matrix.mulVec, dotProduct, hM, dist, sum_mul]
    rw [Fintype.sum_prod_type]
    refine (Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (fun u hu => ?_) fun t => ?_).symm
    · have : u ∉ S := fun h => hu ⟨⟨u, h⟩, rfl⟩
      simp [mPert, hφ, this]
    · refine sum_congr rfl fun v _ => ?_
      by_cases h : x (t.val, v) = a <;> simp [mPert, hφ, h]
  rw [hsum, hz]
  rfl

omit [Fintype β₁] [Fintype β₂] in
/-- `dist` on the line through `q` in the direction `φ`. -/
lemma dist_mPert_line {φ : 𝒰₁ → ℝ} (hφ : dist (mPert q φ) x = 0) (t : ℝ) :
    dist (mPert q fun u => 1 + t * φ u) x = dist q x := by
  classical
  funext a
  have h := congrFun hφ a
  have e : dist (mPert q fun u => 1 + t * φ u) x a = dist q x a + t * dist (mPert q φ) x a := by
    simp only [dist, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun z _ => ?_
    by_cases hz : x z = a <;> simp [mPert, hz]
    ring
  rw [e, h]
  simp

/-- A perturbation that keeps the law of `X` is a pmf, and does not enlarge the support of `U₂`. -/
lemma mPert_props [Finite α] (hq : IsPMF q) {c : 𝒰₁ → ℝ} (hc : ∀ u, 0 ≤ c u)
    (hx : dist (mPert q c) x = dist q x) :
    IsPMF (mPert q c) ∧ mSupp₂ (mPert q c) ⊆ mSupp₂ q := by
  have := Fintype.ofFinite α
  refine ⟨⟨fun z => mul_nonneg (hq.nonneg z) (hc z.1), ?_⟩, fun v hv => ?_⟩
  · have e := fun f : 𝒰₁ × 𝒰₂ → ℝ => sum_dist_mul f x fun _ => (1 : ℝ)
    simp only [mul_one] at e
    rw [← e (mPert q c), hx, e q]
    exact hq.sum_eq_one
  · by_contra hn
    apply mem_mSupp₂.1 hv
    simp only [mMarg₂, mPert]
    exact sum_eq_zero fun u _ => by rw [eq_zero_of_notMem_mSupp₂ hq.nonneg hn u, zero_mul]

variable {T₁ : α → β₁ → ℝ} {T₂ : α → β₂ → ℝ}

/-- **Pages C-9 to C-11 of [elgamal2010].** If `U₁` has more than `|𝒳|` values, one of them can be
removed without decreasing the objective. -/
theorem exists_reduce₁ [Fintype α] (hq : IsPMF q) (hT₁ : IsChannel T₁) (hT₂ : IsChannel T₂)
    (hcard : Fintype.card α < (mSupp₁ q).card) :
    ∃ q', IsPMF q' ∧ (mSupp₁ q').card < (mSupp₁ q).card ∧ mSupp₂ q' ⊆ mSupp₂ q ∧
      martonPhi q x T₁ T₂ ≤ martonPhi q' x T₁ T₂ := by
  classical
  obtain ⟨φ, hφ0, ⟨s, hsS, hs⟩, hφ⟩ := exists_perturbation x hcard
  have hSne : (mSupp₁ q).Nonempty := ⟨s, hsS⟩
  have hmpos : ∀ u ∈ mSupp₁ q, 0 < mMarg₁ q u := fun u hu =>
    lt_of_le_of_ne (sum_nonneg fun v _ => hq.nonneg _) (mem_mSupp₁.1 hu).symm
  -- The mean of `φ` is zero.
  have hmean : ∑ u ∈ mSupp₁ q, mMarg₁ q u * φ u = 0 := by
    have e := sum_dist_mul (mPert q φ) x fun _ => (1 : ℝ)
    simp only [hφ, Pi.zero_apply, sum_const_zero, mul_one] at e
    rw [Fintype.sum_prod_type] at e
    rw [sum_subset (subset_univ _) (fun u _ hu => by rw [hφ0 u hu, mul_zero])]
    rw [e]
    refine sum_congr rfl fun u _ => ?_
    simp only [mMarg₁, mPert, sum_mul]
  obtain ⟨up, hup, hmax⟩ := exists_max_image _ φ hSne
  obtain ⟨um, hum, hmin⟩ := exists_min_image _ φ hSne
  have hP : 0 < φ up := by
    by_contra hn
    push Not at hn
    have h0 := (sum_eq_zero_iff_of_nonpos fun u hu => mul_nonpos_of_nonneg_of_nonpos
      (hmpos u hu).le ((hmax u hu).trans hn)).1 hmean s hsS
    exact hs ((mul_eq_zero.1 h0).resolve_left (hmpos s hsS).ne')
  have hN : φ um < 0 := by
    by_contra hn
    push Not at hn
    have h0 := (sum_eq_zero_iff_of_nonneg fun u hu => mul_nonneg
      (hmpos u hu).le (hn.trans (hmin u hu))).1 hmean s hsS
    exact hs ((mul_eq_zero.1 h0).resolve_left (hmpos s hsS).ne')
  set P := φ up with hPd
  set N := - φ um with hNd
  have hNpos : 0 < N := by simpa [hNd] using hN
  set c₁ : 𝒰₁ → ℝ := fun u => 1 + (-(1 / P)) * φ u with hc₁
  set c₂ : 𝒰₁ → ℝ := fun u => 1 + (1 / N) * φ u with hc₂
  have h₁ : ∀ u, 0 ≤ c₁ u := fun u => by
    by_cases hu : u ∈ mSupp₁ q
    · have := hmax u hu
      simp only [hc₁]
      have e : 1 + -(1 / P) * φ u = (P - φ u) / P := by field_simp; ring
      rw [e]
      exact div_nonneg (by linarith) hP.le
    · simp [hc₁, hφ0 u hu]
  have h₂ : ∀ u, 0 ≤ c₂ u := fun u => by
    by_cases hu : u ∈ mSupp₁ q
    · have := hmin u hu
      simp only [hc₂]
      have e : 1 + 1 / N * φ u = (N + φ u) / N := by field_simp
      rw [e]
      exact div_nonneg (by simp only [hNd]; linarith) hNpos.le
    · simp [hc₂, hφ0 u hu]
  have hx₁ : dist (mPert q c₁) x = dist q x := dist_mPert_line hφ _
  have hx₂ : dist (mPert q c₂) x = dist q x := dist_mPert_line hφ _
  have hPN : 0 < P + N := add_pos hP hNpos
  have hmix := martonPhi_le_mix (T₁ := T₁) (T₂ := T₂) hq.nonneg hT₁ hT₂ h₁ h₂
    (l := P / (P + N)) (m := N / (P + N)) (by positivity) (by positivity) (by field_simp)
    (fun u => by simp only [hc₁, hc₂]; field_simp; ring) hx₁ hx₂
  -- A perturbation with a zero at a point of the support removes this point.
  have hkey : ∀ {c : 𝒰₁ → ℝ} {u₀ : 𝒰₁}, u₀ ∈ mSupp₁ q → c u₀ = 0 →
      (mSupp₁ (mPert q c)).card < (mSupp₁ q).card := fun {c u₀} hu₀ hc₀ => by
    refine card_lt_card ⟨fun u hu => ?_, fun hsub => ?_⟩
    · by_contra hn
      apply mem_mSupp₁.1 hu
      simp only [mMarg₁, mPert]
      exact sum_eq_zero fun v _ => by rw [eq_zero_of_notMem_mSupp₁ hq.nonneg hn v, zero_mul]
    · apply mem_mSupp₁.1 (hsub hu₀)
      simp only [mMarg₁, mPert, hc₀, mul_zero, sum_const_zero]
  have hle : martonPhi q x T₁ T₂ ≤ martonPhi (mPert q c₁) x T₁ T₂ ∨
      martonPhi q x T₁ T₂ ≤ martonPhi (mPert q c₂) x T₁ T₂ := by
    by_contra hn
    push Not at hn
    obtain ⟨hn₁, hn₂⟩ := hn
    have hl : 0 < P / (P + N) := by positivity
    have hm : 0 < N / (P + N) := by positivity
    have hlm : P / (P + N) + N / (P + N) = 1 := by field_simp
    have a₁ := mul_lt_mul_of_pos_left hn₁ hl
    have a₂ := mul_lt_mul_of_pos_left hn₂ hm
    have a₃ : P / (P + N) * martonPhi q x T₁ T₂ + N / (P + N) * martonPhi q x T₁ T₂ =
        martonPhi q x T₁ T₂ := by rw [← add_mul, hlm, one_mul]
    linarith
  rcases hle with hle | hle
  · obtain ⟨hP₁, hS₂⟩ := mPert_props hq h₁ hx₁
    have hz : c₁ up = 0 := by
      change 1 + -(1 / P) * P = 0
      rw [neg_mul, one_div_mul_cancel hP.ne']
      ring
    exact ⟨_, hP₁, hkey hup hz, hS₂, hle⟩
  · obtain ⟨hP₂, hS₂⟩ := mPert_props hq h₂ hx₂
    have hz : c₂ um = 0 := by
      have e : φ um = -N := by simp [hNd]
      simp only [hc₂]
      rw [e, mul_neg, one_div_mul_cancel hNpos.ne']
      ring
    exact ⟨_, hP₂, hkey hum hz, hS₂, hle⟩

/-- **Page C-11 of [elgamal2010].** By induction, `U₁` can be reduced to at most `|𝒳|` values. -/
theorem exists_card_le₁ [Fintype α] (hT₁ : IsChannel T₁) (hT₂ : IsChannel T₂) (x : 𝒰₁ × 𝒰₂ → α)
    (q : 𝒰₁ × 𝒰₂ → ℝ) (hq : IsPMF q) :
    ∃ q', IsPMF q' ∧ (mSupp₁ q').card ≤ Fintype.card α ∧ mSupp₂ q' ⊆ mSupp₂ q ∧
      martonPhi q x T₁ T₂ ≤ martonPhi q' x T₁ T₂ := by
  induction h : (mSupp₁ q).card using Nat.strong_induction_on generalizing q with
  | _ n ih =>
    by_cases hc : n ≤ Fintype.card α
    · exact ⟨q, hq, h ▸ hc, Subset.rfl, le_rfl⟩
    · obtain ⟨q₁, hq₁, hlt, hsub, hle⟩ := exists_reduce₁ (x := x) hq hT₁ hT₂
        (by rw [h]; omega : Fintype.card α < (mSupp₁ q).card)
      obtain ⟨q₂, hq₂, hc₂, hsub₂, hle₂⟩ := ih _ (h ▸ hlt) q₁ hq₁ rfl
      exact ⟨q₂, hq₂, hc₂, hsub₂.trans hsub, hle.trans hle₂⟩

/-! ### Exchanging the two auxiliaries -/

omit [Fintype β₁] [Fintype β₂] in
/-- The objective is symmetric. -/
lemma martonPhi_swap [Fintype β₁] [Fintype β₂] (q : 𝒰₁ × 𝒰₂ → ℝ) (x : 𝒰₁ × 𝒰₂ → α)
    (T₁ : α → β₁ → ℝ) (T₂ : α → β₂ → ℝ) :
    martonPhi (fun z : 𝒰₂ × 𝒰₁ => q z.swap) (fun z => x z.swap) T₂ T₁ = martonPhi q x T₁ T₂ := by
  have eY₁ : mLawY (fun z : 𝒰₂ × 𝒰₁ => q z.swap) (fun z => x z.swap) T₁ = mLawY q x T₁ := by
    funext y
    exact (Equiv.prodComm 𝒰₂ 𝒰₁).sum_comp fun z => q z * T₁ (x z) y
  have eY₂ : mLawY (fun z : 𝒰₂ × 𝒰₁ => q z.swap) (fun z => x z.swap) T₂ = mLawY q x T₂ := by
    funext y
    exact (Equiv.prodComm 𝒰₂ 𝒰₁).sum_comp fun z => q z * T₂ (x z) y
  have eH : entropy (fun z : 𝒰₂ × 𝒰₁ => q z.swap) = entropy q := by
    simp only [entropy_eq_sum_negMulLog]
    exact (Equiv.prodComm 𝒰₂ 𝒰₁).sum_comp fun z => negMulLog (q z)
  simp only [martonPhi, eY₁, eY₂, eH]
  have e₁ : mLaw₁ (fun z : 𝒰₂ × 𝒰₁ => q z.swap) (fun z => x z.swap) T₂ = mLaw₂ q x T₂ := rfl
  have e₂ : mLaw₂ (fun z : 𝒰₂ × 𝒰₁ => q z.swap) (fun z => x z.swap) T₁ = mLaw₁ q x T₁ := rfl
  rw [e₁, e₂]
  ring

/-- Both auxiliaries can be reduced to at most `|𝒳|` values. -/
theorem exists_card_le [Fintype α] (hT₁ : IsChannel T₁) (hT₂ : IsChannel T₂) (x : 𝒰₁ × 𝒰₂ → α)
    (hq : IsPMF q) :
    ∃ q', IsPMF q' ∧ (mSupp₁ q').card ≤ Fintype.card α ∧ (mSupp₂ q').card ≤ Fintype.card α ∧
      martonPhi q x T₁ T₂ ≤ martonPhi q' x T₁ T₂ := by
  obtain ⟨q₁, hq₁, hc₁, -, hle₁⟩ := exists_card_le₁ hT₁ hT₂ x q hq
  have hs₁ : IsPMF fun z : 𝒰₂ × 𝒰₁ => q₁ z.swap :=
    ⟨fun z => hq₁.nonneg _, by
      rw [← hq₁.sum_eq_one]
      exact (Equiv.prodComm 𝒰₂ 𝒰₁).sum_comp q₁⟩
  obtain ⟨q₂, hq₂, hc₂, hsub, hle₂⟩ := exists_card_le₁ hT₂ hT₁ (fun z => x z.swap) _ hs₁
  rw [martonPhi_swap] at hle₂
  have e : martonPhi q₂ (fun z => x z.swap) T₂ T₁ =
      martonPhi (fun z : 𝒰₁ × 𝒰₂ => q₂ z.swap) x T₁ T₂ := by
    have h := martonPhi_swap (fun z : 𝒰₁ × 𝒰₂ => q₂ z.swap) x T₁ T₂
    simpa only [Prod.swap_swap] using h
  refine ⟨fun z => q₂ z.swap, ⟨fun z => hq₂.nonneg _, ?_⟩, ?_, ?_, hle₁.trans (hle₂.trans e.le)⟩
  · rw [← hq₂.sum_eq_one]
    exact (Equiv.prodComm 𝒰₁ 𝒰₂).sum_comp q₂
  · have hsub' : mSupp₁ (fun z : 𝒰₁ × 𝒰₂ => q₂ z.swap) ⊆ mSupp₁ q₁ := fun u hu => by
      have h1 : u ∈ mSupp₂ q₂ := hu |> fun h => by simpa [mem_mSupp₁, mem_mSupp₂, mMarg₁, mMarg₂]
        using h
      have h2 := hsub h1
      simpa [mem_mSupp₁, mem_mSupp₂, mMarg₁, mMarg₂] using h2
    exact (card_le_card hsub').trans hc₁
  · have : mSupp₂ (fun z : 𝒰₁ × 𝒰₂ => q₂ z.swap) = mSupp₁ q₂ := by
      ext v
      simp [mem_mSupp₁, mem_mSupp₂, mMarg₁, mMarg₂]
    rw [this]
    exact hc₂

/-! ### Relabelling -/

section Relabel

variable {𝒲₁ 𝒲₂ : Type*} [Fintype 𝒲₁] [Fintype 𝒲₂] {e₁ : 𝒲₁ → 𝒰₁} {e₂ : 𝒲₂ → 𝒰₂}

/-- The objective does not change when the supports are relabelled. -/
theorem martonPhi_relabel (he₁ : e₁.Injective) (he₂ : e₂.Injective)
    (hq : ∀ z, q z ≠ 0 → z.1 ∈ Set.range e₁ ∧ z.2 ∈ Set.range e₂) (x : 𝒰₁ × 𝒰₂ → α)
    (T₁ : α → β₁ → ℝ) (T₂ : α → β₂ → ℝ) :
    martonPhi (fun z : 𝒲₁ × 𝒲₂ => q (e₁ z.1, e₂ z.2)) (fun z => x (e₁ z.1, e₂ z.2)) T₁ T₂ =
      martonPhi q x T₁ T₂ := by
  have h0₁ : ∀ u v, u ∉ Set.range e₁ → q (u, v) = 0 := fun u v hu => by
    by_contra hn
    exact hu (hq _ hn).1
  have h0₂ : ∀ u v, v ∉ Set.range e₂ → q (u, v) = 0 := fun u v hv => by
    by_contra hn
    exact hv (hq _ hn).2
  have hinj : (Prod.map e₁ e₂).Injective := he₁.prodMap he₂
  have h0 : ∀ z, z ∉ Set.range (Prod.map e₁ e₂) → q z = 0 := fun z hz => by
    by_contra hn
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hq z hn
    exact hz ⟨(a, b), Prod.ext ha hb⟩
  have eY₁ : mLawY (fun z : 𝒲₁ × 𝒲₂ => q (e₁ z.1, e₂ z.2)) (fun z => x (e₁ z.1, e₂ z.2)) T₁ =
      mLawY q x T₁ := by
    funext y
    exact Fintype.sum_of_injective _ hinj _ _ (fun z hz => by rw [h0 z hz, zero_mul]) fun _ => rfl
  have eY₂ : mLawY (fun z : 𝒲₁ × 𝒲₂ => q (e₁ z.1, e₂ z.2)) (fun z => x (e₁ z.1, e₂ z.2)) T₂ =
      mLawY q x T₂ := by
    funext y
    exact Fintype.sum_of_injective _ hinj _ _ (fun z hz => by rw [h0 z hz, zero_mul]) fun _ => rfl
  have eH : entropy (fun z : 𝒲₁ × 𝒲₂ => q (e₁ z.1, e₂ z.2)) = entropy q := by
    simp only [entropy_eq_sum_negMulLog]
    exact Fintype.sum_of_injective _ hinj _ _ (fun z hz => by rw [h0 z hz, negMulLog_zero])
      fun _ => rfl
  have e₁' : entropy (mLaw₁ (fun z : 𝒲₁ × 𝒲₂ => q (e₁ z.1, e₂ z.2))
      (fun z => x (e₁ z.1, e₂ z.2)) T₁) = entropy (mLaw₁ q x T₁) := by
    simp only [entropy_eq_sum_negMulLog]
    refine Fintype.sum_of_injective (Prod.map e₁ id) (he₁.prodMap Function.injective_id) _ _
      (fun s hs => ?_) fun s => ?_
    · have hu : s.1 ∉ Set.range e₁ := fun ⟨a, ha⟩ => hs ⟨(a, s.2), Prod.ext ha rfl⟩
      have : mLaw₁ q x T₁ s = 0 := sum_eq_zero fun v _ => by rw [h0₁ _ _ hu, zero_mul]
      rw [this, negMulLog_zero]
    · congr 1
      exact Fintype.sum_of_injective _ he₂ _ _ (fun v hv => by rw [h0₂ _ _ hv, zero_mul])
        fun _ => rfl
  have e₂' : entropy (mLaw₂ (fun z : 𝒲₁ × 𝒲₂ => q (e₁ z.1, e₂ z.2))
      (fun z => x (e₁ z.1, e₂ z.2)) T₂) = entropy (mLaw₂ q x T₂) := by
    simp only [entropy_eq_sum_negMulLog]
    refine Fintype.sum_of_injective (Prod.map e₂ id) (he₂.prodMap Function.injective_id) _ _
      (fun s hs => ?_) fun s => ?_
    · have hv : s.1 ∉ Set.range e₂ := fun ⟨a, ha⟩ => hs ⟨(a, s.2), Prod.ext ha rfl⟩
      have : mLaw₂ q x T₂ s = 0 := sum_eq_zero fun u _ => by rw [h0₂ _ _ hv, zero_mul]
      rw [this, negMulLog_zero]
    · congr 1
      exact Fintype.sum_of_injective _ he₁ _ _ (fun u hu => by rw [h0₁ _ _ hu, zero_mul])
        fun _ => rfl
  simp only [martonPhi, eY₁, eY₂, eH, e₁', e₂']

end Relabel

/-- **The bound on pages C-9 to C-11 of [elgamal2010].** For every `p(u₁, u₂)` and `x(u₁, u₂)` there
are `p'` and `x'` with `|𝒰₁'| = |𝒰₂'| = |𝒳|` and at least the same value of
`I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)`. -/
theorem exists_marton_card [Fintype α] {W : α → β₁ × β₂ → ℝ} (hq : IsPMF q) (hW : IsChannel W)
    (x : 𝒰₁ × 𝒰₂ → α) :
    ∃ (q' : Fin (Fintype.card α) × Fin (Fintype.card α) → ℝ)
      (x' : Fin (Fintype.card α) × Fin (Fintype.card α) → α),
      IsPMF q' ∧ martonSum q x W ≤ martonSum q' x' W := by
  classical
  obtain ⟨z₀⟩ : Nonempty (𝒰₁ × 𝒰₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  obtain ⟨q₂, hq₂, hc₁, hc₂, hle⟩ := exists_card_le (x := x) hW.bcMarg₁ hW.bcMarg₂ hq
  -- Restrict to the supports.
  set S₁ := {u // u ∈ mSupp₁ q₂}
  set S₂ := {v // v ∈ mSupp₂ q₂}
  have hre : martonPhi (fun z : S₁ × S₂ => q₂ (z.1.val, z.2.val)) (fun z => x (z.1.val, z.2.val))
      (bcMarg₁ W) (bcMarg₂ W) = martonPhi q₂ x (bcMarg₁ W) (bcMarg₂ W) := by
    refine martonPhi_relabel Subtype.val_injective Subtype.val_injective (fun z hz => ?_) _ _ _
    refine ⟨⟨⟨z.1, ?_⟩, rfl⟩, ⟨⟨z.2, ?_⟩, rfl⟩⟩
    · by_contra hn
      exact hz (eq_zero_of_notMem_mSupp₁ hq₂.nonneg hn z.2)
    · by_contra hn
      exact hz (eq_zero_of_notMem_mSupp₂ hq₂.nonneg hn z.1)
  have hsum : ∑ z : S₁ × S₂, q₂ (z.1.val, z.2.val) = 1 := by
    rw [← hq₂.sum_eq_one]
    refine Fintype.sum_of_injective (Prod.map Subtype.val Subtype.val)
      (Subtype.val_injective.prodMap Subtype.val_injective) _ _ (fun z hz => ?_) fun _ => rfl
    by_contra hn
    refine hz ⟨(⟨z.1, ?_⟩, ⟨z.2, ?_⟩), rfl⟩
    · by_contra hu
      exact hn (eq_zero_of_notMem_mSupp₁ hq₂.nonneg hu z.2)
    · by_contra hv
      exact hn (eq_zero_of_notMem_mSupp₂ hq₂.nonneg hv z.1)
  -- Embed the supports in `Fin |𝒳|`.
  obtain ⟨ψ₁⟩ : Nonempty (S₁ ↪ Fin (Fintype.card α)) :=
    Function.Embedding.nonempty_of_card_le (by simpa [S₁] using hc₁)
  obtain ⟨ψ₂⟩ : Nonempty (S₂ ↪ Fin (Fintype.card α)) :=
    Function.Embedding.nonempty_of_card_le (by simpa [S₂] using hc₂)
  have hinj : (Prod.map ψ₁ ψ₂).Injective := ψ₁.injective.prodMap ψ₂.injective
  set q₄ : Fin (Fintype.card α) × Fin (Fintype.card α) → ℝ :=
    Function.extend (Prod.map ψ₁ ψ₂) (fun z : S₁ × S₂ => q₂ (z.1.val, z.2.val)) 0 with hq₄
  set x₄ : Fin (Fintype.card α) × Fin (Fintype.card α) → α :=
    Function.extend (Prod.map ψ₁ ψ₂) (fun z : S₁ × S₂ => x (z.1.val, z.2.val))
      fun _ => x z₀ with hx₄
  have hq₄e : ∀ z : S₁ × S₂, q₄ (ψ₁ z.1, ψ₂ z.2) = q₂ (z.1.val, z.2.val) := fun z =>
    hinj.extend_apply _ _ z
  have hx₄e : ∀ z : S₁ × S₂, x₄ (ψ₁ z.1, ψ₂ z.2) = x (z.1.val, z.2.val) := fun z =>
    hinj.extend_apply _ _ z
  have hq₄0 : ∀ z, z ∉ Set.range (Prod.map ψ₁ ψ₂) → q₄ z = 0 := fun z hz => by
    rw [hq₄, Function.extend_apply' _ _ _ fun ⟨t, ht⟩ => hz ⟨t, ht⟩]
    rfl
  have hsum₄ : ∑ z, q₄ z = 1 := by
    rw [← hsum]
    exact (Fintype.sum_of_injective _ hinj _ _ hq₄0 fun z => (hq₄e z).symm).symm
  have hP₄ : IsPMF q₄ := by
    refine ⟨fun z => ?_, hsum₄⟩
    by_cases hz : z ∈ Set.range (Prod.map ψ₁ ψ₂)
    · obtain ⟨t, rfl⟩ := hz
      exact (hq₄e t).symm ▸ hq₂.nonneg _
    · rw [hq₄0 z hz]
  have hre₄ := martonPhi_relabel (q := q₄) (e₁ := ψ₁) (e₂ := ψ₂) ψ₁.injective ψ₂.injective
    (fun z hz => by
      by_contra hn
      apply hz
      refine hq₄0 z fun ⟨t, ht⟩ => hn ?_
      exact ⟨⟨t.1, congrArg Prod.fst ht⟩, ⟨t.2, congrArg Prod.snd ht⟩⟩) x₄ (bcMarg₁ W) (bcMarg₂ W)
  simp only [hq₄e, hx₄e] at hre₄
  refine ⟨q₄, x₄, hP₄, ?_⟩
  rw [martonSum_eq_martonPhi hq hW, martonSum_eq_martonPhi hP₄ hW, ← hre₄, hre]
  exact hle

/-- The objective is continuous in the law. -/
lemma continuous_martonPhi (x : 𝒰₁ × 𝒰₂ → α) (T₁ : α → β₁ → ℝ) (T₂ : α → β₂ → ℝ) :
    Continuous fun q : 𝒰₁ × 𝒰₂ → ℝ => martonPhi q x T₁ T₂ := by
  simp only [martonPhi, entropy_eq_sum_negMulLog, mLawY, mLaw₁, mLaw₂]
  refine Continuous.sub (Continuous.sub (Continuous.add (Continuous.add ?_ ?_) ?_) ?_) ?_ <;>
    exact continuous_finsetSum _ fun _ _ => continuous_negMulLog.comp (by fun_prop)

universe u v in
/-- **The maximum sum rate on page C-9 of [elgamal2010].** The maximum of
`I(U₁; Y₁) + I(U₂; Y₂) - I(U₁; U₂)` over all finite alphabets, all `p(u₁, u₂)` and all `x(u₁, u₂)`
exists, and is attained with `|𝒰₁| = |𝒰₂| = |𝒳|`. -/
theorem exists_isMax_martonSum [Fintype α] [Nonempty α] {W : α → β₁ × β₂ → ℝ} (hW : IsChannel W) :
    ∃ (q' : Fin (Fintype.card α) × Fin (Fintype.card α) → ℝ)
      (x' : Fin (Fintype.card α) × Fin (Fintype.card α) → α), IsPMF q' ∧
      ∀ (𝒱₁ : Type u) (𝒱₂ : Type v) [Fintype 𝒱₁] [Fintype 𝒱₂] (r : 𝒱₁ × 𝒱₂ → ℝ) (f : 𝒱₁ × 𝒱₂ → α),
        IsPMF r → martonSum r f W ≤ martonSum q' x' W := by
  classical
  have hn : 0 < Fintype.card α := Fintype.card_pos
  have hne : Nonempty (Fin (Fintype.card α) × Fin (Fintype.card α)) :=
    ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  have hbest : ∀ f : Fin (Fintype.card α) × Fin (Fintype.card α) → α,
      ∃ q ∈ {q : Fin (Fintype.card α) × Fin (Fintype.card α) → ℝ | IsPMF q},
        IsMaxOn (fun q => martonPhi q f (bcMarg₁ W) (bcMarg₂ W)) {q | IsPMF q} q := fun f =>
    isCompact_setOf_isPMF.exists_isMaxOn ⟨uniformPMF _, uniformPMF_isPMF⟩
      (continuous_martonPhi f _ _).continuousOn
  choose b hb hmax using hbest
  obtain ⟨f₀, hf₀⟩ := Finite.exists_max fun f => martonPhi (b f) f (bcMarg₁ W) (bcMarg₂ W)
  refine ⟨b f₀, f₀, hb f₀, fun 𝒱₁ 𝒱₂ _ _ r f hr => ?_⟩
  obtain ⟨q', x', hq', hle⟩ := exists_marton_card hr hW f
  refine hle.trans ?_
  rw [martonSum_eq_martonPhi hq' hW, martonSum_eq_martonPhi (hb f₀) hW]
  exact (hmax x' hq').trans (hf₀ x')

end InfoTheory
