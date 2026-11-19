/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DetNetwork

/-!
# Finite-field deterministic networks

Each node receives a linear function of the inputs, over a finite field: `Y_k = ∑_j g_{jk} X_j`. The
uniform product input maximizes the information across all the cuts, so the capacity is the smallest
rank of a cut.

## Main definitions

* `ffdF g`: the outputs of the network.
* `ffdG g S`: the matrix of a cut, with `Y(Sᶜ) = G(S) X(S) + G'(S) X(Sᶜ)`.

## Main statements

* `cutInfo_ffd_le`: the information across a cut is at most `rank G(S) log q`.
* `cutInfo_ffd_uniform`: the uniform product input achieves it.
* `mnCapacity_ffd`: **the capacity of a finite-field deterministic multicast network, page 19-21**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset Module

@[expose] public noncomputable section

namespace InfoTheory

variable {N : ℕ} {F : Type*} [Field F] [Fintype F]

/-- **Page 19-21 of [elgamal2010].** The outputs of a finite-field deterministic network. -/
def ffdF (g : Fin N → Fin N → F) (x : Fin N → F) (k : Fin N) : F := ∑ j, g j k * x j

/-- **Page 19-21 of [elgamal2010].** The matrix `G(S)` of a cut. -/
def ffdG (g : Fin N → Fin N → F) (S : Finset (Fin N)) : Matrix ↥(Sᶜ : Finset (Fin N)) ↥S F :=
  Matrix.of fun l j => g j l

/-- The matrix `G'(S)` of a cut. -/
def ffdG' (g : Fin N → Fin N → F) (S : Finset (Fin N)) :
    Matrix ↥(Sᶜ : Finset (Fin N)) ↥(Sᶜ : Finset (Fin N)) F :=
  Matrix.of fun l j => g j l

omit [Fintype F] in
/-- `Y(Sᶜ) = G(S) X(S) + G'(S) X(Sᶜ)`. -/
lemma restr_ffdF (g : Fin N → Fin N → F) (S : Finset (Fin N)) (x : Fin N → F) :
    (restr Sᶜ (ffdF g x) : ↥(Sᶜ : Finset (Fin N)) → F) =
      (ffdG g S).mulVec (restr S x) + (ffdG' g S).mulVec (restr Sᶜ x) := by
  funext l
  simp only [restr, ffdF, Pi.add_apply, Matrix.mulVec, dotProduct, ffdG, ffdG', Matrix.of_apply]
  rw [Finset.sum_coe_sort S fun j => g j l * x j,
    Finset.sum_coe_sort Sᶜ fun j => g j l * x j, sum_add_sum_compl]

/-- The conditional entropy of the output across a cut is the conditional entropy of `G(S) X(S)`. -/
lemma condEntropy_ffd {p : (Fin N → F) → ℝ} (hp : IsPMF p) (g : Fin N → Fin N → F)
    (S : Finset (Fin N)) :
    H[fun x : Fin N → F => (restr Sᶜ (ffdF g x) : ↥(Sᶜ : Finset (Fin N)) → F) |
      fun x => (restr Sᶜ x : ↥(Sᶜ : Finset (Fin N)) → F) ; p] =
    H[fun x : Fin N → F => (ffdG g S).mulVec (restr S x) |
      fun x => (restr Sᶜ x : ↥(Sᶜ : Finset (Fin N)) → F) ; p] := by
  rw [condEntropy_eq_sub hp, condEntropy_eq_sub hp]
  congr 1
  refine entropyRV_eq_of_injective p
    (fun t : (↥(Sᶜ : Finset (Fin N)) → F) × (↥(Sᶜ : Finset (Fin N)) → F) =>
      (t.1, t.2 + (ffdG' g S).mulVec t.1)) (fun a b h => ?_) fun x => ?_
  · simp only [Prod.mk.injEq] at h
    refine Prod.ext h.1 ?_
    have := h.2
    rw [h.1] at this
    exact add_right_cancel this
  · simp only [pair]
    rw [restr_ffdF]

/-- The logarithm of the number of elements of the range of a matrix. -/
lemma log_card_range {m k : Type*} [Fintype k] (A : Matrix m k F)
    [Fintype (LinearMap.range A.mulVecLin)] :
    log (Fintype.card (LinearMap.range A.mulVecLin)) = A.rank * log (Fintype.card F) := by
  rw [card_eq_pow_finrank (K := F), Nat.cast_pow, log_pow, Matrix.finrank_range_mulVecLin]

/-- The logarithm of the number of elements of the kernel of a matrix. -/
lemma log_card_ker {m k : Type*} [Fintype k] (A : Matrix m k F)
    [Fintype (LinearMap.ker A.mulVecLin)] :
    log (Fintype.card (LinearMap.ker A.mulVecLin)) =
      ((Fintype.card k : ℝ) - A.rank) * log (Fintype.card F) := by
  rw [card_eq_pow_finrank (K := F), Nat.cast_pow, log_pow]
  congr 1
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [finrank_fintype_fun_eq_card] at h
  have h₂ : A.rank = finrank F (LinearMap.range A.mulVecLin) :=
    (Matrix.finrank_range_mulVecLin A).symm
  rw [h₂, ← h]
  push_cast
  ring

/-- **Page 19-21 of [elgamal2010].** The information across a cut is at most `rank G(S) log q`. -/
theorem cutInfo_ffd_le {p : (Fin N → F) → ℝ} (hp : IsPMF p) (g : Fin N → Fin N → F)
    (S : Finset (Fin N)) :
    cutInfo (X := fun _ => F) (Y := fun _ => F) p (detW (ffdF g)) S ≤
      (ffdG g S).rank * log (Fintype.card F) := by
  classical
  rw [cutInfo_detW hp]
  have h₁ := condEntropy_ffd hp g S
  refine (le_of_eq h₁).trans ?_
  set A := ffdG g S with hA
  have : Fintype (LinearMap.range A.mulVecLin) := Fintype.ofFinite _
  let u : (Fin N → F) → LinearMap.range A.mulVecLin := fun x =>
    ⟨A.mulVec (restr S x), LinearMap.mem_range.mpr ⟨_, rfl⟩⟩
  have h₂ : H[fun x : Fin N → F => A.mulVec (restr S x) ; p] = H[u ; p] :=
    entropyRV_eq_of_injective p (Subtype.val) Subtype.val_injective fun _ => rfl
  have h₃ := condEntropy_le_entropy hp (fun x : Fin N → F => A.mulVec (restr S x))
    fun x => (restr Sᶜ x : ↥(Sᶜ : Finset (Fin N)) → F)
  have h₄ := entropyRV_le_log_card hp u
  rw [log_card_range] at h₄
  linarith

omit [Field F] in
/-- The uniform product law. -/
lemma prodLaw_uniform : prodLaw (fun _ : Fin N => uniformPMF F) = uniformPMF (Fin N → F) := by
  funext x
  simp [prodLaw, uniformPMF]

/-- **Page 19-21 of [elgamal2010].** The uniform product input achieves `rank G(S) log q`. -/
theorem cutInfo_ffd_uniform (g : Fin N → Fin N → F) (S : Finset (Fin N)) :
    cutInfo (X := fun _ => F) (Y := fun _ => F) (prodLaw fun _ : Fin N => uniformPMF F)
      (detW (ffdF g)) S = (ffdG g S).rank * log (Fintype.card F) := by
  classical
  have : Nonempty F := ⟨0⟩
  have hp' : IsPMF (uniformPMF (Fin N → F)) := uniformPMF_isPMF
  have hp : IsPMF (prodLaw fun _ : Fin N => uniformPMF F) := by
    rw [prodLaw_uniform]
    exact hp'
  refine le_antisymm (cutInfo_ffd_le hp g S) ?_
  rw [prodLaw_uniform] at hp ⊢
  rw [cutInfo_detW hp, condEntropy_ffd hp]
  set μ := uniformPMF (Fin N → F)
  set Am := ffdG g S with hAm
  have hlogq : 0 ≤ log (Fintype.card F) := log_natCast_nonneg _
  let A : (Fin N → F) → ↥S → F := fun x => restr S x
  let B : (Fin N → F) → ↥(Sᶜ : Finset (Fin N)) → F := fun x => restr Sᶜ x
  let W₀ : (Fin N → F) → ↥(Sᶜ : Finset (Fin N)) → F := fun x => Am.mulVec (A x)
  -- the entropy of the inputs of the cut
  have hHx : H[id ; μ] = N * log (Fintype.card F) := by
    rw [entropyRV, dist_id, entropy_uniformPMF, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
      log_pow]
  have hAB : H[pair B A ; μ] = H[id ; μ] :=
    entropyRV_eq_of_injective μ (fun x : Fin N → F => (restr Sᶜ x, restr S x))
      (restr_compl_restr_injective (γ := fun _ => F) S) fun _ => rfl
  have hB : H[B ; μ] ≤ (Sᶜ.card : ℝ) * log (Fintype.card F) := by
    refine (entropyRV_le_log_card hp' B).trans_eq ?_
    rw [Fintype.card_fun, Fintype.card_coe, Nat.cast_pow, log_pow]
  have hcard : (S.card : ℝ) + Sᶜ.card = N := by
    have := card_add_card_compl S
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hAgB : (S.card : ℝ) * log (Fintype.card F) ≤ H[A | B ; μ] := by
    rw [condEntropy_eq_sub hp', hAB, hHx]
    nlinarith
  -- the entropy of the inputs given the outputs of the matrix
  have hsplit : H[A | B ; μ] ≤ H[W₀ | B ; μ] + H[A | W₀ ; μ] := by
    have e₁ : H[pair W₀ A | B ; μ] = H[A | B ; μ] :=
      condEntropy_congr_left hp' B (fun a => (Am.mulVec a, a))
        (fun a b h => (Prod.mk.inj h).2) fun _ => rfl
    have e₂ := chain_rule_cond hp' W₀ A B
    have e₃ := condEntropy_le_condEntropy hp' A B W₀
    have e₄ : H[A | pair W₀ B ; μ] = H[A | pair B W₀ ; μ] :=
      condEntropy_congr_right hp' A Prod.swap Prod.swap_injective fun _ => rfl
    rw [e₄] at e₂
    linarith
  -- the kernel
  have : Fintype (LinearMap.ker Am.mulVecLin) := Fintype.ofFinite _
  let sec : (↥(Sᶜ : Finset (Fin N)) → F) → ↥S → F := fun w =>
    if h : ∃ a, Am.mulVec a = w then Classical.choose h else 0
  have hsec : ∀ a, Am.mulVec (sec (Am.mulVec a)) = Am.mulVec a := fun a => by
    have h : ∃ a', Am.mulVec a' = Am.mulVec a := ⟨a, rfl⟩
    simp only [sec, h, dite_true]
    exact Classical.choose_spec h
  let φ : (Fin N → F) → LinearMap.ker Am.mulVecLin := fun x =>
    ⟨A x - sec (W₀ x), by
      rw [LinearMap.mem_ker, map_sub, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hsec,
        sub_self]⟩
  have hker : H[A | W₀ ; μ] ≤ ((S.card : ℝ) - Am.rank) * log (Fintype.card F) := by
    have e₁ : H[A | W₀ ; μ] = H[φ | W₀ ; μ] := by
      rw [condEntropy_eq_sub hp', condEntropy_eq_sub hp']
      congr 1
      refine entropyRV_eq_of_injective μ
        (fun t : (↥(Sᶜ : Finset (Fin N)) → F) × LinearMap.ker Am.mulVecLin =>
          (t.1, (t.2 : ↥S → F) + sec t.1)) (fun a b h => ?_) fun x => ?_
      · simp only [Prod.mk.injEq] at h
        refine Prod.ext h.1 (Subtype.ext ?_)
        have := h.2
        rw [h.1] at this
        exact add_right_cancel this
      · simp [pair, φ, W₀]
    have e₂ := condEntropy_le_entropy hp' φ W₀
    have e₃ := entropyRV_le_log_card hp' φ
    rw [log_card_ker, Fintype.card_coe] at e₃
    linarith
  have hfin : (Am.rank : ℝ) * log (Fintype.card F) ≤ H[W₀ | B ; μ] := by
    nlinarith
  exact hfin

/-- **Page 19-21 of [elgamal2010]: the capacity of a finite-field deterministic multicast network**
is `min_{k ∈ D} min_{S : s ∈ S, k ∈ Sᶜ} rank G(S) log q`. -/
theorem mnCapacity_ffd (g : Fin N → Fin N → F) {s : Fin N} {D : Finset (Fin N)}
    (hD : ∀ k ∈ D, s ≠ k) {k₀ : Fin N} {S₀ : Finset (Fin N)} (hk₀ : k₀ ∈ D) (hS₀ : s ∈ S₀)
    (hkS₀ : k₀ ∉ S₀)
    (hmin : ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S → k ∉ S → (ffdG g S₀).rank ≤ (ffdG g S).rank) :
    mnCapacity (X := fun _ => F) (Y := fun _ => F) (detW (ffdF g)) s D * log 2 =
      (ffdG g S₀).rank * log (Fintype.card F) := by
  classical
  have : Nonempty F := ⟨0⟩
  have hlogq : 0 ≤ log (Fintype.card F) := log_natCast_nonneg _
  refine mnCapacity_det_eq (X := fun _ => F) (Y := fun _ => F) (px := fun _ => uniformPMF F)
    (fun _ => uniformPMF_isPMF) hD (fun p hp k _ S _ _ => ?_) (fun k hk S hs hkS => ?_)
    hk₀ hS₀ hkS₀ (cutInfo_ffd_uniform g S₀)
  · rw [cutInfo_ffd_uniform]
    exact cutInfo_ffd_le hp g S
  · rw [cutInfo_ffd_uniform]
    refine mul_le_mul_of_nonneg_right ?_ hlogq
    exact_mod_cast hmin k hk S hs hkS

end InfoTheory
