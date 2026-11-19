/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DetFiniteField

/-!
# Deterministic networks with no interference

Each node receives a collection of functions of one input each:
`Y_k = (y_{k1}(X_1), …, y_{kN}(X_N))`. The cutset bound is achieved by a product input law.

## Main definitions

* `niF a`: the outputs of the network.
* `niH a S j q`: `H({Y_{lj} : l ∈ Sᶜ})` for the law `q` of `X_j`.
* `niBound a s D`: the bound of page 19-20.

## Main statements

* `entropy_prodLaw`: the entropy of an independent family is the sum of the entropies.
* `cutInfo_ni_le`: the information across a cut is at most the sum over the nodes of the cut, for
  the marginal laws.
* `cutInfo_ni_prod`: for a product law, they are equal.
* `mnCapacity_ni`: **the capacity of a deterministic multicast network with no interference**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*} [∀ k, Fintype (A k)]

/-- **The entropy of an independent family is the sum of the entropies.** -/
theorem entropy_prodLaw {ν : ∀ k, A k → ℝ} (hν : ∀ k, IsPMF (ν k)) :
    entropy (prodLaw ν) = ∑ k, entropy (ν k) := by
  classical
  have h₁ : ∀ c : ∀ k, A k, negMulLog (prodLaw ν c) =
      ∑ k, (∏ j, ν j (c j)) * -log (ν k (c k)) := by
    intro c
    by_cases h : ∀ k, ν k (c k) ≠ 0
    · simp only [negMulLog, prodLaw]
      rw [log_prod fun k _ => h k, ← mul_sum, sum_neg_distrib]
      ring
    · push Not at h
      obtain ⟨k, hk⟩ := h
      have h0 : ∏ j, ν j (c j) = 0 := prod_eq_zero (mem_univ k) hk
      simp [prodLaw, h0]
  simp only [entropy_eq_sum_negMulLog]
  simp_rw [h₁]
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [sum_prodLaw_mul_apply hν k fun a => -log (ν k a)]
  exact sum_congr rfl fun a _ => by simp [negMulLog]

end Family

section Marg

variable {N : ℕ} {A : Fin N → Type*} [∀ k, Fintype (A k)]

/-- The marginal of an independent family on a set of indices. -/
lemma sum_prodLaw_ind_restr {μ : ∀ k, A k → ℝ} (hμ : ∀ k, IsPMF (μ k)) (S : Finset (Fin N))
    (t : ∀ j : S, A j) :
    ∑ r : ∀ k, A k, prodLaw μ r * ind (restr S r = t) = prodLaw (fun j : S => μ j) t := by
  classical
  have h₁ : ∀ r : ∀ k, A k, prodLaw μ r * ind (restr S r = t) =
      ∏ k, (μ k (r k) * if h : k ∈ S then ind (r k = t ⟨k, h⟩) else 1) := by
    intro r
    rw [prod_mul_distrib]
    congr 1
    by_cases h : restr S r = t
    · rw [ind_of_pos h]
      refine (prod_eq_one fun k _ => ?_).symm
      by_cases hk : k ∈ S
      · rw [dite_eq_left hk]
        exact ind_of_pos (congrFun h ⟨k, hk⟩)
      · rw [dite_eq_right hk]
    · rw [ind_of_neg h]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp h
      refine (prod_eq_zero (mem_univ (j : Fin N)) ?_).symm
      rw [dite_eq_left j.property]
      exact ind_of_neg hj
  simp_rw [h₁]
  rw [sum_prod_pi (A := A) fun k a => μ k a * if h : k ∈ S then ind (a = t ⟨k, h⟩) else 1]
  have h₂ : ∀ k, ∑ a : A k, μ k a * (if h : k ∈ S then ind (a = t ⟨k, h⟩) else 1) =
      if h : k ∈ S then μ k (t ⟨k, h⟩) else 1 := by
    intro k
    by_cases hk : k ∈ S
    · simp only [hk, dite_true]
      rw [Finset.sum_eq_single (t ⟨k, hk⟩)]
      · rw [ind_of_pos rfl, mul_one]
      · exact fun a _ ha => by rw [ind_of_neg ha, mul_zero]
      · simp
    · simp only [hk, dite_false, mul_one]
      exact (hμ k).sum_eq_one
  simp_rw [h₂]
  have h₃ : ∏ k, (if h : k ∈ S then μ k (t ⟨k, h⟩) else 1) =
      ∏ k ∈ S, (if h : k ∈ S then μ k (t ⟨k, h⟩) else 1) := by
    refine (prod_subset (subset_univ S) fun k _ hk => ?_).symm
    rw [dite_eq_right hk]
  rw [h₃, ← Finset.prod_coe_sort S]
  refine prod_congr rfl fun j _ => ?_
  rw [dite_eq_left j.property]

/-- The law of the part of an independent family on a set of indices. -/
lemma dist_prodLaw_restr {C : Fin N → Type*} [∀ k, Finite (C k)] {ν : ∀ k, A k → ℝ}
    (hν : ∀ k, IsPMF (ν k)) (φ : ∀ k, A k → C k) (S : Finset (Fin N)) :
    dist (prodLaw ν) (fun x (j : S) => φ j (x j)) =
      prodLaw (fun j : S => dist (ν j) (φ j)) := by
  classical
  have : ∀ k, Fintype (C k) := fun k => Fintype.ofFinite _
  funext t
  have h₁ := sum_prodLaw_comp ν φ fun r => ind (restr S r = t)
  have h₂ := sum_prodLaw_ind_restr (μ := fun k => dist (ν k) (φ k)) (fun k => (hν k).dist _) S t
  rw [← h₂, ← h₁]
  simp only [dist, ind]
  refine sum_congr rfl fun x _ => ?_
  have e : (restr S fun k => φ k (x k)) = fun j : S => φ j (x j) := rfl
  rw [e]
  split_ifs <;> simp

end Marg

section Network

variable {N : ℕ} {X : Fin N → Type*} [∀ k, Fintype (X k)] {A : Fin N → Fin N → Type*}
  [∀ l j, Fintype (A l j)]

/-- **Page 19-20 of [elgamal2010].** The outputs of a deterministic network with no interference:
node `k` receives `a k j (x_j)` from node `j`. -/
def niF (a : ∀ l j, X j → A l j) (x : ∀ k, X k) (k : Fin N) : ∀ j, A k j := fun j => a k j (x j)

/-- The components of the outputs of the nodes of `Sᶜ` that come from node `j`. -/
def niT (a : ∀ l j, X j → A l j) (S : Finset (Fin N)) (j : Fin N) (x : X j) :
    ∀ l : (Sᶜ : Finset (Fin N)), A l j := fun l => a l j x

/-- **Page 19-20 of [elgamal2010].** `H({Y_{lj} : l ∈ Sᶜ})`, for the law `q` of `X_j`. -/
def niH (a : ∀ l j, X j → A l j) (S : Finset (Fin N)) (j : Fin N) (q : X j → ℝ) : ℝ :=
  entropy (dist q (niT a S j))

variable {a : ∀ l j, X j → A l j}

/-- The conditional entropy of the outputs across a cut is the conditional entropy of the components
that come from the nodes of the cut. -/
lemma condEntropy_ni {p : (∀ k, X k) → ℝ} (hp : IsPMF p) (S : Finset (Fin N)) :
    H[fun x => restr Sᶜ (niF a x) | restr Sᶜ ; p] =
      H[fun (x : ∀ k, X k) (j : S) => niT a S j (x j) | restr Sᶜ ; p] := by
  classical
  rw [condEntropy_eq_sub hp, condEntropy_eq_sub hp]
  congr 1
  refine entropyRV_eq_of_comp₂ hp
    (fun t : (∀ l : (Sᶜ : Finset (Fin N)), X l) × ∀ j : S, ∀ l : (Sᶜ : Finset (Fin N)), A l j =>
      (t.1, fun (l : (Sᶜ : Finset (Fin N))) (j : Fin N) =>
        if h : j ∈ S then t.2 ⟨j, h⟩ l else a l j (t.1 ⟨j, mem_compl.mpr h⟩)))
    (fun t : (∀ l : (Sᶜ : Finset (Fin N)), X l) × ∀ l : (Sᶜ : Finset (Fin N)), ∀ j, A l j =>
      (t.1, fun (j : S) (l : (Sᶜ : Finset (Fin N))) => t.2 l j)) (fun x => ?_) fun x => rfl
  refine Prod.ext rfl ?_
  funext l j
  by_cases h : j ∈ S
  · simp [pair, niF, niT, restr, h]
  · simp [pair, niF, restr, h]

/-- **Page 19-20 of [elgamal2010].** The information across a cut is at most the sum over the nodes
of the cut, for the marginal laws. -/
theorem cutInfo_ni_le {p : (∀ k, X k) → ℝ} (hp : IsPMF p) (S : Finset (Fin N)) :
    cutInfo p (detW (niF a)) S ≤ ∑ j ∈ S, niH a S j (dist p fun x => x j) := by
  classical
  rw [cutInfo_detW hp, condEntropy_ni hp]
  have h₁ := condEntropy_restr_le hp (β := fun j => ∀ l : (Sᶜ : Finset (Fin N)), A l j)
    (fun (x : ∀ k, X k) j => niT a S j (x j)) (restr Sᶜ) S
  refine h₁.trans (sum_le_sum fun j _ => ?_)
  refine (condEntropy_le_entropy hp _ _).trans_eq ?_
  rw [niH, ← dist_comp_eq]
  rfl

/-- **Page 19-20 of [elgamal2010].** For a product law, the information across a cut is the sum over
the nodes of the cut. -/
theorem cutInfo_ni_prod {px : ∀ k, X k → ℝ} (hpx : ∀ k, IsPMF (px k)) (S : Finset (Fin N)) :
    cutInfo (prodLaw px) (detW (niF a)) S = ∑ j ∈ S, niH a S j (px j) := by
  classical
  have hp := prodLaw_isPMF hpx
  rw [cutInfo_detW hp, condEntropy_ni hp]
  set U : (∀ k, X k) → ∀ j : S, ∀ l : (Sᶜ : Finset (Fin N)), A l j :=
    fun x j => niT a S j (x j) with hU
  have hsumT : ∀ T : Finset (Fin N), H[restr T ; prodLaw px] = ∑ k ∈ T, entropy (px k) := by
    intro T
    have e := dist_prodLaw_restr hpx (fun _ => id) T
    have e₂ : (restr T : (∀ k, X k) → ∀ j : T, X j) = fun x (j : T) => id (x j) := rfl
    rw [entropyRV, e₂, e, entropy_prodLaw (ν := fun j : T => dist (px j) id)
      fun j => (hpx j).dist _, ← Finset.sum_coe_sort T fun k => entropy (px k)]
    refine sum_congr rfl fun j _ => ?_
    rw [dist_id]
  -- the two sides of the cut are independent
  have hindep : I[restr S : restr Sᶜ ; prodLaw px] = 0 := by
    rw [mutualInfo_eq_add_sub hp]
    have h₁ : H[pair (restr S) (restr Sᶜ) ; prodLaw px] = H[restr Sᶜ ∘ id ; prodLaw px] +
        H[restr S ; prodLaw px] := by
      have e₁ : H[pair (restr S) (restr Sᶜ) ; prodLaw px] = H[id ; prodLaw px] :=
        entropyRV_eq_of_injective _ (fun x : ∀ k, X k => (restr S x, restr Sᶜ x))
          (fun u v h => restr_compl_restr_injective (γ := X) S
            (Prod.ext (Prod.ext_iff.mp h).2 (Prod.ext_iff.mp h).1)) fun _ => rfl
      have e₂ : H[id ; prodLaw px] = ∑ k, entropy (px k) := by
        rw [entropyRV, dist_id, entropy_prodLaw hpx]
      have e₃ := sum_add_sum_compl S fun k => entropy (px k)
      have e₄ : H[restr Sᶜ ∘ id ; prodLaw px] = ∑ k ∈ Sᶜ, entropy (px k) := hsumT Sᶜ
      rw [e₁, e₂, e₄, hsumT S, ← e₃]
      ring
    rw [h₁, hsumT S]
    have e₄ : H[restr Sᶜ ∘ id ; prodLaw px] = ∑ k ∈ Sᶜ, entropy (px k) := hsumT Sᶜ
    rw [e₄, hsumT Sᶜ]
    ring
  have hle : I[U : restr Sᶜ ; prodLaw px] ≤ 0 := by
    have h₁ : I[U : restr Sᶜ ; prodLaw px] = I[restr Sᶜ : U ; prodLaw px] := mutualInfo_comm hp _ _
    have h₂ := mutualInfo_comp_le hp (restr Sᶜ) (restr S)
      fun (t : ∀ j : S, X j) (j : S) => niT a S j (t j)
    rw [h₁]
    refine h₂.trans ?_
    rw [mutualInfo_comm hp, hindep]
  have hI := mutualInfo_eq_entropy_sub_condEntropy hp U (restr Sᶜ)
  have hnn := mutualInfo_nonneg hp U (restr Sᶜ)
  have hHU : H[U ; prodLaw px] = ∑ j ∈ S, niH a S j (px j) := by
    rw [entropyRV, hU, dist_prodLaw_restr hpx (niT a S) S,
      entropy_prodLaw (ν := fun j : S => dist (px j) (niT a S j)) fun j => (hpx j).dist _,
      ← Finset.sum_coe_sort S fun j => niH a S j (px j)]
    rfl
  rw [← hHU]
  linarith

/-- **Page 19-20 of [elgamal2010].** The bound
`max_{∏ p(x_k)} min_{k ∈ D} min_{S : s ∈ S, k ∈ Sᶜ} ∑_{j ∈ S} H({Y_{lj} : l ∈ Sᶜ})`, in nats. -/
def niBound (a : ∀ l j, X j → A l j) (s : Fin N) (D : Finset (Fin N)) : ℝ :=
  sSup {v | ∃ px : ∀ k, X k → ℝ, (∀ k, IsPMF (px k)) ∧ ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S →
    k ∉ S → v ≤ ∑ j ∈ S, niH a S j (px j)}

/-- **Page 19-20 of [elgamal2010]: the capacity of a deterministic multicast network with no
interference.** -/
theorem mnCapacity_ni [∀ k, Nonempty (X k)] {s k₀ : Fin N} {D : Finset (Fin N)} (hk₀ : k₀ ∈ D)
    (hs : s ≠ k₀) : mnCapacity (Y := fun k => ∀ j, A k j) (detW (niF a)) s D * log 2 =
      niBound a s D := by
  classical
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hW := detW_isChannel (X := X) (Y := fun k => ∀ j, A k j) (f := niF a)
  have hbddR := bddAbove_isAchievableMN hW hk₀ hs
  have hC0 : 0 ≤ mnCapacity (detW (niF a)) s D := le_csSup hbddR (isAchievableMN_zero s D)
  have hbddV : BddAbove {v | ∃ px : ∀ k, X k → ℝ, (∀ k, IsPMF (px k)) ∧ ∀ k ∈ D,
      ∀ S : Finset (Fin N), s ∈ S → k ∉ S → v ≤ ∑ j ∈ S, niH a S j (px j)} := by
    refine ⟨log (Fintype.card (∀ l : (({s} : Finset (Fin N))ᶜ : Finset (Fin N)), ∀ j, A l j)), ?_⟩
    rintro v ⟨px, hpx, h⟩
    refine (h k₀ hk₀ {s} (mem_singleton_self s) (by simpa using hs.symm)).trans ?_
    rw [← cutInfo_ni_prod hpx]
    exact cutInfo_le_log_card (prodLaw_isPMF hpx) hW _
  refine le_antisymm ?_ ?_
  · rw [← le_div_iff₀ hlog]
    have hb0 : 0 ≤ niBound a s D := by
      refine le_csSup hbddV ⟨fun _ => uniformPMF _, fun _ => uniformPMF_isPMF, fun k _ S _ _ => ?_⟩
      exact sum_nonneg fun j _ => entropy_nonneg (uniformPMF_isPMF.dist _)
    refine Real.sSup_le (fun R hR => ?_) (div_nonneg hb0 hlog.le)
    rw [le_div_iff₀ hlog]
    obtain ⟨p, hp, hle⟩ := IsAchievableMN.exists_cutset hW hR
    refine le_csSup hbddV ⟨fun j => dist p fun x => x j, fun j => hp.dist _, fun k hk S hsS hkS =>
      ?_⟩
    exact (hle k hk S hsS hkS).trans (cutInfo_ni_le hp S)
  · refine Real.sSup_le (fun v hv => ?_) (mul_nonneg hC0 hlog.le)
    obtain ⟨px, hpx, hle⟩ := hv
    by_cases hv0 : v ≤ 0
    · exact hv0.trans (mul_nonneg hC0 hlog.le)
    push Not at hv0
    rw [← div_le_iff₀ hlog]
    refine le_of_forall_lt_imp_le_of_dense fun R hR => ?_
    by_cases hR0 : 0 ≤ R
    · refine le_csSup hbddR (isAchievableMN_det hpx hR0 fun d hd S hsS hdS => ?_)
      rw [cutInfo_ni_prod hpx]
      exact ((lt_div_iff₀ hlog).mp hR).trans_le (hle d hd S hsS hdS)
    · exact (not_le.mp hR0).le.trans hC0

end Network

end InfoTheory
