/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.PiLaw

/-!
# Noisy network coding: the single-letter law and the fresh codewords

Noisy network coding fixes independent inputs `p(x₁) ⋯ p(x_N)` and compression channels
`p(v_k | y_k, x_k)`, where `V_k` is the `Ŷ_k` of the notes. This file defines the resulting law on
`(Xᴺ, Yᴺ, Vᴺ)` and bounds the probability that a tuple of sequences is typical, when the sequences
of the nodes of `S` are fresh.

## Main definitions

* `nncLaw px W τ`: the law `∏ p(x_k) p(yᴺ | xᴺ) ∏ p(v_k | y_k, x_k)`.
* `nncLd L d`: the law of what destination `d` tests, `(Xᴺ, Y_d, Vᴺ)`.
* `nncTest`: the test of the decoder of `d`.
* `nncJ L S d`: the exponent of the probability of the test, for the set `S` of fresh nodes,
  `∑_{k ∈ S} (H(X_k) + H(V_k | X_k)) - H(X(S), V(S) | X(Sᶜ), V(Sᶜ), Y_d)`.

## Main statements

* `sum_nnc_fresh_le`: **the bound for the fresh nodes**: whatever the law of the sequences of the
  nodes of `Sᶜ`, the probability of the test is about `exp(-n J(S))`.

## Implementation notes

The notes bound the probability of the test on page 19-33 by "the joint typicality lemma (check!)",
with the true compression indices. Since the law of the sequences of the nodes of `Sᶜ` does not
matter here, the same bound covers the indices of `Sᶜ` that differ from the true ones.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Law

variable {N : ℕ} {X Y V : Fin N → Type*}

/-- The single-letter sample space of noisy network coding. -/
abbrev NNCΩ (X Y V : Fin N → Type*) := (∀ k, X k) × (∀ k, Y k) × (∀ k, V k)

/-- The law `∏ p(x_k) p(yᴺ | xᴺ) ∏ p(v_k | y_k, x_k)`. -/
def nncLaw (px : ∀ k, X k → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (τ : ∀ k, X k × Y k → V k → ℝ)
    (ω : NNCΩ X Y V) : ℝ :=
  (∏ k, px k (ω.1 k)) * W ω.1 ω.2.1 * ∏ k, τ k (ω.1 k, ω.2.1 k) (ω.2.2 k)

variable [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)]
  {px : ∀ k, X k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {τ : ∀ k, X k × Y k → V k → ℝ}

/-- The sum over the compressions. -/
lemma sum_nncLaw_mul (hτ : ∀ k, IsChannel (τ k)) (g : (∀ k, X k) → (∀ k, Y k) → ℝ) :
    ∑ ω, nncLaw px W τ ω * g ω.1 ω.2.1 = ∑ x, ∑ y, (∏ k, px k (x k)) * W x y * g x y := by
  simp only [Fintype.sum_prod_type, nncLaw]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  have h : ∑ v : ∀ k, V k, ∏ k, τ k (x k, y k) (v k) = 1 := by
    rw [sum_prod_pi]
    exact prod_eq_one fun k _ => (hτ k _).sum_eq_one
  calc _ = (∏ k, px k (x k)) * W x y * g x y * ∑ v : ∀ k, V k, ∏ k, τ k (x k, y k) (v k) := by
        rw [mul_sum]
        exact sum_congr rfl fun v _ => by ring
    _ = _ := by rw [h, mul_one]

lemma nncLaw_isPMF (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k)) :
    IsPMF (nncLaw px W τ) := by
  refine ⟨fun ω => mul_nonneg (mul_nonneg (prod_nonneg fun k _ => (hpx k).nonneg _)
    ((hW _).nonneg _)) (prod_nonneg fun k _ => (hτ k _).nonneg _), ?_⟩
  have h := sum_nncLaw_mul (px := px) (W := W) hτ fun _ _ => 1
  simp only [mul_one] at h
  rw [h]
  have h₂ : ∀ x : ∀ k, X k, ∑ y, (∏ k, px k (x k)) * W x y = ∏ k, px k (x k) := fun x => by
    rw [← mul_sum, (hW x).sum_eq_one, mul_one]
  simp_rw [h₂]
  exact (prodLaw_isPMF hpx).sum_eq_one

/-- The law of one member of an independent family. -/
lemma sum_prodLaw_mul_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] {ν : ∀ k, A k → ℝ} (hν : ∀ k, IsPMF (ν k)) (j : ι) (h : A j → ℝ) :
    ∑ x : ∀ k, A k, (∏ k, ν k (x k)) * h (x j) = ∑ a, ν j a * h a := by
  classical
  have h₁ : ∀ x : ∀ k, A k, (∏ k, ν k (x k)) * h (x j) =
      ∑ a, ν j a * h a * (ind (x j = a) * ∏ k ∈ univ.erase j, ν k (x k)) := by
    intro x
    rw [Finset.sum_eq_single (x j)]
    · rw [ind_of_pos rfl, one_mul, ← mul_prod_erase univ _ (mem_univ j)]
      ring
    · intro a _ ha
      rw [ind_of_neg (Ne.symm ha)]
      ring
    · simp
  simp_rw [h₁]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← mul_sum, sum_ind_prod_erase hν j a, mul_one]

/-- The law of the input of a node is `p(x_k)`. -/
lemma dist_nncLaw_x (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    (k : Fin N) : dist (nncLaw px W τ) (fun ω => ω.1 k) = px k := by
  classical
  funext a
  have h₁ : dist (nncLaw px W τ) (fun ω => ω.1 k) a =
      ∑ ω, nncLaw px W τ ω * ind (ω.1 k = a) := by
    simp only [dist, ind]
    refine sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp
  have h₂ := sum_nncLaw_mul (px := px) (W := W) hτ fun x _ => ind (x k = a)
  rw [h₁, h₂]
  have h₃ : ∀ x : ∀ k, X k, ∑ y, (∏ k, px k (x k)) * W x y * ind (x k = a) =
      (∏ k, px k (x k)) * ind (x k = a) := fun x => by
    rw [← sum_mul, ← mul_sum, (hW x).sum_eq_one, mul_one]
  simp_rw [h₃]
  rw [sum_prodLaw_mul_apply hpx k fun b => ind (b = a), Finset.sum_eq_single a]
  · rw [ind_of_pos rfl, mul_one]
  · intro b _ hb
    rw [ind_of_neg hb, mul_zero]
  · simp

variable (L : NNCΩ X Y V → ℝ)

/-- The law of what destination `d` tests, `(Xᴺ, Y_d, Vᴺ)`. -/
def nncLd (d : Fin N) : (∀ k, X k) × Y d × (∀ k, V k) → ℝ :=
  dist L fun ω => (ω.1, ω.2.1 d, ω.2.2)

/-- The law of the pair `(X_k, V_k)`. -/
def nncRho (k : Fin N) : X k × V k → ℝ := dist L fun ω => (ω.1 k, ω.2.2 k)

/-- The variables of the side `S` of a cut. -/
def nncF (S : Finset (Fin N)) (ω : NNCΩ X Y V) : (∀ k : S, X k) × (∀ k : S, V k) :=
  (restr S ω.1, restr S ω.2.2)

/-- The variables of the side `Sᶜ` of a cut, with the output of `d`. -/
def nncZ (S : Finset (Fin N)) (d : Fin N) (ω : NNCΩ X Y V) :
    ((∀ k : (Sᶜ : Finset (Fin N)), X k) × (∀ k : (Sᶜ : Finset (Fin N)), V k)) × Y d :=
  ((restr Sᶜ ω.1, restr Sᶜ ω.2.2), ω.2.1 d)

/-- The entropies of a fresh sequence of node `k`, `H(X_k) + H(V_k | X_k)`. -/
def nncHk (k : Fin N) : ℝ :=
  H[fun ω : NNCΩ X Y V => ω.1 k ; L] + H[Prod.snd | Prod.fst ; nncRho L k]

/-- **Page 19-33 of [elgamal2010].** The exponent of the probability of the test, for the set `S` of
fresh nodes: `∑_{k ∈ S} (H(X_k) + H(V_k | X_k)) - H(X(S), V(S) | X(Sᶜ), V(Sᶜ), Y_d)`. -/
def nncJ (S : Finset (Fin N)) (d : Fin N) : ℝ :=
  ∑ k ∈ S, nncHk L k - H[nncF S | nncZ S d ; L]

/-- The constant in front of the typicality parameter in the bound for the fresh nodes. -/
def nncC (S : Finset (Fin N)) (d : Fin N) : ℝ :=
  ∑ k ∈ S, nncHk L k + H[nncF S | nncZ S d ; L]

variable {n : ℕ}

/-- The tuple of sequences that destination `d` tests. -/
def nncTuple (d : Fin N) (c : ∀ k, (Fin n → X k) × (Fin n → V k)) (yd : Fin n → Y d) :
    Fin n → (∀ k, X k) × Y d × (∀ k, V k) :=
  fun i => (fun k => (c k).1 i, yd i, fun k => (c k).2 i)

/-- **Page 19-31 of [elgamal2010].** The test of the decoder of `d`. -/
def nncTest (d : Fin N) (ε : ℝ) (c : ∀ k, (Fin n → X k) × (Fin n → V k)) (yd : Fin n → Y d) :
    Prop :=
  nncTuple d c yd ∈ robustTypicalSet (nncLd L d) n ε

variable {L}

/-- A passed test gives a bound on the probability of the sequences of a node. -/
lemma nncTest_iid_le (hL : IsPMF L) {d : Fin N} {ε : ℝ}
    {c : ∀ k, (Fin n → X k) × (Fin n → V k)} {yd : Fin n → Y d} (h : nncTest L d ε c yd)
    (k : Fin N) :
    iidPMF (dist L fun ω : NNCΩ X Y V => ω.1 k) n (c k).1 ≤
      exp (-(n * (H[fun ω : NNCΩ X Y V => ω.1 k ; L] -
        ε * H[fun ω : NNCΩ X Y V => ω.1 k ; L]))) := by
  have hm := comp_mem_robustTypicalSet h fun t : (∀ k, X k) × Y d × (∀ k, V k) => t.1 k
  have e : dist (nncLd L d) (fun t : (∀ k, X k) × Y d × (∀ k, V k) => t.1 k) =
      dist L fun ω : NNCΩ X Y V => ω.1 k := by
    rw [nncLd, ← dist_comp_eq]
    rfl
  rw [e] at hm
  exact iidPMF_le_of_mem_robustTypicalSet (hL.dist _) hm

/-- A passed test gives a bound on the conditional probability of the compression of a node. -/
lemma nncTest_chan_le (hL : IsPMF L) {d : Fin N} {ε : ℝ} {q : ∀ k, X k → V k → ℝ}
    (hq : ∀ k a b, nncRho L k (a, b) = dist L (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    {c : ∀ k, (Fin n → X k) × (Fin n → V k)} {yd : Fin n → Y d} (h : nncTest L d ε c yd)
    (k : Fin N) :
    seqChan (q k) n (c k).1 (c k).2 ≤
      exp (-(n * (H[Prod.snd | Prod.fst ; nncRho L k] -
        ε * H[Prod.snd | Prod.fst ; nncRho L k]))) := by
  have hm := comp_mem_robustTypicalSet h fun t : (∀ k, X k) × Y d × (∀ k, V k) => (t.1 k, t.2.2 k)
  have e : dist (nncLd L d) (fun t : (∀ k, X k) × Y d × (∀ k, V k) => (t.1 k, t.2.2 k)) =
      nncRho L k := by
    rw [nncLd, ← dist_comp_eq]
    rfl
  rw [e] at hm
  have hρ : IsPMF (nncRho L k) := hL.dist _
  have hm' : zipSeq (c k).1 (c k).2 ∈ robustTypicalSet (nncRho L k) n ε := hm
  have hb := channelExt_condPMF_le_of_mem hρ hm'
  refine le_trans (le_of_eq ?_) hb
  simp only [seqChan, channelExt]
  refine prod_congr rfl fun i _ => ?_
  have hpos := pos_of_mem_robustTypicalSet hρ.nonneg hm' i
  have hzip : zipSeq (c k).1 (c k).2 i = ((c k).1 i, (c k).2 i) := rfl
  rw [hzip] at hpos
  have hρ₁ : marg (nncRho L k) ((c k).1 i) = dist L (fun ω : NNCΩ X Y V => ω.1 k) ((c k).1 i) := by
    rw [marg_eq_dist]
    have : dist (nncRho L k) Prod.fst = dist L fun ω : NNCΩ X Y V => ω.1 k := by
      rw [nncRho, ← dist_comp_eq]
      rfl
    rw [this]
  have hne : dist L (fun ω : NNCΩ X Y V => ω.1 k) ((c k).1 i) ≠ 0 := by
    intro h0
    rw [hq, h0, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [condPMF, hρ₁, hq]
  field_simp

/-- A family from its parts on `S` and outside `S`. -/
def nncMerge (S : Finset (Fin N)) (cS : ∀ k : S, (Fin n → X k) × (Fin n → V k))
    (cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k)) (k : Fin N) :
    (Fin n → X k) × (Fin n → V k) :=
  if h : k ∈ S then cS ⟨k, h⟩ else cC ⟨k, h⟩

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] in
lemma nncMerge_left {S : Finset (Fin N)} (cS : ∀ k : S, (Fin n → X k) × (Fin n → V k))
    (cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k)) (k : S) :
    nncMerge S cS cC k = cS k := by
  simp [nncMerge]

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, Fintype (V k)] in
lemma nncMerge_right {S : Finset (Fin N)} (cS : ∀ k : S, (Fin n → X k) × (Fin n → V k))
    (cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k)) (k : {k // k ∉ S}) :
    nncMerge S cS cC k = cC k := by
  simp [nncMerge, k.2]

open Classical in
/-- **The number of tuples of fresh sequences that pass the test.** -/
lemma card_nnc_fresh_le (hL : IsPMF L) (S : Finset (Fin N)) (d : Fin N) (ε : ℝ)
    (yd : Fin n → Y d) (cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k)) :
    ((univ.filter fun cS : (∀ k : S, (Fin n → X k) × (Fin n → V k)) =>
      nncTest L d ε (nncMerge S cS cC) yd).card : ℝ) ≤
      exp (n * (H[nncF S | nncZ S d ; L] + ε * H[nncF S | nncZ S d ; L])) := by
  set L' := dist L (pair (nncZ S d) (nncF S : NNCΩ X Y V → _)) with hL'
  have hL'P : IsPMF L' := hL.dist _
  have hH : H[Prod.snd | Prod.fst ; L'] = H[nncF S | nncZ S d ; L] := by
    refine condEntropy_eq_of_dist_pair_eq hL'P hL ?_
    rw [hL', pair_fst_snd, dist_id]
  let z : Fin n → ((∀ k : (Sᶜ : Finset (Fin N)), X k) × (∀ k : (Sᶜ : Finset (Fin N)), V k)) × Y d :=
    fun i => ((fun k => (cC ⟨k, mem_compl.mp k.2⟩).1 i, fun k => (cC ⟨k, mem_compl.mp k.2⟩).2 i),
      yd i)
  let φ : (∀ k : S, (Fin n → X k) × (Fin n → V k)) → Fin n → (∀ k : S, X k) × (∀ k : S, V k) :=
    fun cS i => (fun k => (cS k).1 i, fun k => (cS k).2 i)
  have hφ : Function.Injective φ := by
    intro a b hab
    funext k
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact congrFun (Prod.ext_iff.mp (congrFun hab i)).1 k
    · exact congrFun (Prod.ext_iff.mp (congrFun hab i)).2 k
  have hcard := card_condRobustTypicalSet_le hL'P ε z
  rw [hH] at hcard
  refine le_trans ?_ hcard
  have hsub : (univ.filter fun cS : (∀ k : S, (Fin n → X k) × (Fin n → V k)) =>
      nncTest L d ε (nncMerge S cS cC) yd).card ≤ (condRobustTypicalSet L' ε z).card := by
    refine card_le_card_of_injOn φ (fun cS hcS => ?_) hφ.injOn
    have hT := (mem_filter.mp hcS).2
    have hm := comp_mem_robustTypicalSet hT fun t : (∀ k, X k) × Y d × (∀ k, V k) =>
      (((restr Sᶜ t.1, restr Sᶜ t.2.2), t.2.1), (restr S t.1, restr S t.2.2))
    have e : dist (nncLd L d) (fun t : (∀ k, X k) × Y d × (∀ k, V k) =>
        (((restr Sᶜ t.1, restr Sᶜ t.2.2), t.2.1), (restr S t.1, restr S t.2.2))) = L' := by
      rw [nncLd, ← dist_comp_eq]
      rfl
    rw [e] at hm
    refine mem_condRobustTypicalSet.mpr ?_
    convert hm using 1
    funext i
    refine Prod.ext (Prod.ext (Prod.ext (funext fun k => ?_) (funext fun k => ?_)) rfl)
      (Prod.ext (funext fun k => ?_) (funext fun k => ?_))
    · change (cC ⟨k, _⟩).1 i = (nncMerge S cS cC k).1 i
      rw [nncMerge_right cS cC ⟨k, mem_compl.mp k.2⟩]
    · change (cC ⟨k, _⟩).2 i = (nncMerge S cS cC k).2 i
      rw [nncMerge_right cS cC ⟨k, mem_compl.mp k.2⟩]
    · change (cS k).1 i = (nncMerge S cS cC k).1 i
      rw [nncMerge_left cS cC k]
    · change (cS k).2 i = (nncMerge S cS cC k).2 i
      rw [nncMerge_left cS cC k]
  exact_mod_cast hsub

/-- **The bound for the fresh nodes.** Let `(c_k)` be independent, with the sequences of the nodes
of `S` fresh, and the sequences of the other nodes arbitrary. Then the probability of the test is
about `exp(-n J(S))`. The factors `a k` are the total masses of the laws of the nodes. -/
theorem sum_nnc_fresh_le (hL : IsPMF L) {q : ∀ k, X k → V k → ℝ}
    (hq : ∀ k a b, nncRho L k (a, b) = dist L (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    (hqc : ∀ k, IsChannel (q k)) (S : Finset (Fin N)) (d : Fin N) {ε : ℝ} (a : Fin N → ℝ)
    (ha : ∀ k, 0 ≤ a k) (μ : ∀ k, (Fin n → X k) × (Fin n → V k) → ℝ) (hμ0 : ∀ k c, 0 ≤ μ k c)
    (hS : ∀ k ∈ S, ∀ c, μ k c ≤ a k * (iidPMF (dist L fun ω : NNCΩ X Y V => ω.1 k) n c.1 *
      seqChan (q k) n c.1 c.2))
    (hSc : ∀ k, k ∉ S → ∑ c, μ k c ≤ a k) (yd : Fin n → Y d) :
    ∑ c : ∀ k, (Fin n → X k) × (Fin n → V k), (∏ k, μ k (c k)) * ind (nncTest L d ε c yd) ≤
      (∏ k, a k) * exp (-(n * (nncJ L S d - ε * nncC L S d))) := by
  classical
  set e := Equiv.piEquivPiSubtypeProd (fun k => k ∈ S)
    (fun k => (Fin n → X k) × (Fin n → V k)) with he
  -- the bound for fixed sequences of the nodes of `Sᶜ`
  set E₁ := exp (-(n * (∑ k ∈ S, nncHk L k - ε * ∑ k ∈ S, nncHk L k))) with hE₁
  set E₂ := exp (n * (H[nncF S | nncZ S d ; L] + ε * H[nncF S | nncZ S d ; L])) with hE₂
  have hA : 0 ≤ ∏ k ∈ S, a k := prod_nonneg fun k _ => ha k
  have hin : ∀ cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k),
      ∑ cS : ∀ k : S, (Fin n → X k) × (Fin n → V k), (∏ k : S, μ k (cS k)) *
        ind (nncTest L d ε (nncMerge S cS cC) yd) ≤ (∏ k ∈ S, a k) * (E₁ * E₂) := by
    intro cC
    have hbd : ∀ cS : ∀ k : S, (Fin n → X k) × (Fin n → V k),
        nncTest L d ε (nncMerge S cS cC) yd → ∏ k : S, μ k (cS k) ≤ (∏ k ∈ S, a k) * E₁ := by
      intro cS hT
      have hk : ∀ k : S, μ k (cS k) ≤ a k * exp (-(n * (nncHk L k - ε * nncHk L k))) := by
        intro k
        have h₁ := nncTest_iid_le hL hT k
        have h₂ := nncTest_chan_le hL hq hT k
        rw [nncMerge_left cS cC k] at h₁ h₂
        refine (hS k k.2 (cS k)).trans (mul_le_mul_of_nonneg_left ?_ (ha k))
        calc _ ≤ exp (-(n * (H[fun ω : NNCΩ X Y V => ω.1 k ; L] -
                ε * H[fun ω : NNCΩ X Y V => ω.1 k ; L]))) *
              exp (-(n * (H[Prod.snd | Prod.fst ; nncRho L k] -
                ε * H[Prod.snd | Prod.fst ; nncRho L k]))) :=
              mul_le_mul h₁ h₂ ((seqChan_isChannel (hqc k) n _).nonneg _) (exp_pos _).le
          _ = _ := by
              rw [← exp_add]
              congr 1
              simp only [nncHk]
              ring
      calc _ ≤ ∏ k : S, (a k * exp (-(n * (nncHk L k - ε * nncHk L k)))) :=
            prod_le_prod₀ (fun k _ => hμ0 k _) fun k _ => hk k
        _ = _ := by
            rw [prod_mul_distrib, Finset.prod_coe_sort S a,
              Finset.prod_coe_sort S fun k => exp (-(n * (nncHk L k - ε * nncHk L k))),
              ← exp_sum, hE₁]
            congr 2
            rw [Finset.mul_sum, ← sum_sub_distrib, Finset.mul_sum, sum_neg_distrib]
    have hcnt := card_nnc_fresh_le hL S d ε yd cC
    calc _ ≤ ∑ cS : ∀ k : S, (Fin n → X k) × (Fin n → V k), ((∏ k ∈ S, a k) * E₁) *
          ind (nncTest L d ε (nncMerge S cS cC) yd) := by
          refine sum_le_sum fun cS _ => ?_
          by_cases hT : nncTest L d ε (nncMerge S cS cC) yd
          · rw [ind_of_pos hT, mul_one, mul_one]
            exact hbd cS hT
          · rw [ind_of_neg hT, mul_zero, mul_zero]
      _ = ((∏ k ∈ S, a k) * E₁) * ((univ.filter fun cS : (∀ k : S, (Fin n → X k) × (Fin n → V k)) =>
          nncTest L d ε (nncMerge S cS cC) yd).card : ℝ) := by
          rw [← mul_sum]
          congr 1
          simp only [ind]
          rw [sum_boole]
      _ ≤ ((∏ k ∈ S, a k) * E₁) * E₂ :=
          mul_le_mul_of_nonneg_left hcnt (mul_nonneg hA (exp_pos _).le)
      _ = _ := mul_assoc _ _ _
  -- the sum over the sequences of the nodes of `Sᶜ`
  have hsub : ∀ f : Fin N → ℝ, ∏ k : {k // k ∉ S}, f k = ∏ k ∈ Sᶜ, f k := by
    intro f
    rw [← Finset.prod_coe_sort Sᶜ f]
    exact Fintype.prod_equiv (Equiv.subtypeEquivRight fun k => by simp) _ _ fun k => rfl
  have hsplit : ∀ cS cC, ∏ k, μ k (nncMerge S cS cC k) =
      (∏ k : S, μ k (cS k)) * ∏ k : {k // k ∉ S}, μ k (cC k) := by
    intro cS cC
    have h₁ : ∏ k : S, μ k (cS k) = ∏ k : S, μ k (nncMerge S cS cC k) :=
      prod_congr rfl fun k _ => by rw [nncMerge_left cS cC k]
    have h₂ : ∏ k : {k // k ∉ S}, μ k (cC k) = ∏ k : {k // k ∉ S}, μ k (nncMerge S cS cC k) :=
      prod_congr rfl fun k _ => by rw [nncMerge_right cS cC k]
    rw [h₁, h₂, Finset.prod_coe_sort S fun k => μ k (nncMerge S cS cC k),
      hsub fun k => μ k (nncMerge S cS cC k)]
    exact (prod_mul_prod_compl S _).symm
  have hsum : ∑ c : ∀ k, (Fin n → X k) × (Fin n → V k), (∏ k, μ k (c k)) *
      ind (nncTest L d ε c yd) = ∑ cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k),
        (∏ k : {k // k ∉ S}, μ k (cC k)) * ∑ cS : ∀ k : S, (Fin n → X k) × (Fin n → V k),
          (∏ k : S, μ k (cS k)) * ind (nncTest L d ε (nncMerge S cS cC) yd) := by
    rw [← Fintype.sum_equiv e.symm (fun p => (∏ k, μ k (e.symm p k)) *
      ind (nncTest L d ε (e.symm p) yd)) _ fun _ => rfl, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun cC _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun cS _ => ?_
    have h₁ : e.symm (cS, cC) = nncMerge S cS cC := rfl
    simp only [h₁]
    rw [hsplit]
    ring
  rw [hsum]
  have hC : ∑ cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k),
      ∏ k : {k // k ∉ S}, μ k (cC k) ≤ ∏ k ∈ Sᶜ, a k := by
    rw [sum_prod_pi (A := fun k : {k // k ∉ S} => (Fin n → X k) × (Fin n → V k))
      fun k c => μ k c]
    rw [← hsub a]
    exact prod_le_prod₀ (fun k _ => sum_nonneg fun c _ => hμ0 k c) fun k _ => hSc k k.2
  have hE : E₁ * E₂ = exp (-(n * (nncJ L S d - ε * nncC L S d))) := by
    rw [hE₁, hE₂, ← exp_add]
    congr 1
    simp only [nncJ, nncC]
    ring
  have hP : (∏ k ∈ Sᶜ, a k) * ∏ k ∈ S, a k = ∏ k, a k := by
    rw [mul_comm]
    exact prod_mul_prod_compl S a
  have hprod0 : ∀ cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k),
      0 ≤ ∏ k : {k // k ∉ S}, μ k (cC k) := fun cC => prod_nonneg fun k _ => hμ0 k _
  calc _ ≤ ∑ cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k),
        (∏ k : {k // k ∉ S}, μ k (cC k)) * ((∏ k ∈ S, a k) * (E₁ * E₂)) :=
        sum_le_sum fun cC _ => mul_le_mul_of_nonneg_left (hin cC) (hprod0 cC)
    _ = (∑ cC : ∀ k : {k // k ∉ S}, (Fin n → X k) × (Fin n → V k),
        ∏ k : {k // k ∉ S}, μ k (cC k)) * ((∏ k ∈ S, a k) * (E₁ * E₂)) := (sum_mul _ _ _).symm
    _ ≤ (∏ k ∈ Sᶜ, a k) * ((∏ k ∈ S, a k) * (E₁ * E₂)) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg hA (mul_nonneg (exp_pos _).le (exp_pos _).le))
    _ = _ := by rw [← mul_assoc, hP, hE]

end Law

end InfoTheory
