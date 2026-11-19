/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.KeyMultiNode

/-!
# Secret key agreement with many nodes: the converse

The converse of Theorem 9 of Lecture 23 of El Gamal and Kim, on pages 23-56 to 23-59.

## Main statements

* `MultiKeyCode.mul_zCondH_le`: the rates `R'ⱼ` of the notes are in the region of omniscience.
* `MultiKeyCode.entropy_key_le`: `H(K) ≤ n (H(X^N | Z) - R_CFO) + N η + I(K; Zⁿ, Mᵠ)`.
* `IsAchievableMultiKey.le`: the converse of Theorem 9.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section Split

variable {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c] {μ : Ω → ℝ}

/-- If `G` is a function of `(V, Z)`, then `H(V | Z) = H(G | Z) + H(V | G, Z)`. -/
lemma condEntropy_split (hμ : IsPMF μ) (V : Ω → a) (G : Ω → b) (Z : Ω → c) (φ : a × c → b)
    (hG : G = φ ∘ pair V Z) : H[V | Z ; μ] = H[G | Z ; μ] + H[V | pair G Z ; μ] := by
  have h₁ := chain_rule_cond hμ V G Z
  have h₂ := chain_rule_cond hμ G V Z
  have h₃ : H[pair V G | Z ; μ] = H[pair G V | Z ; μ] :=
    condEntropy_congr_left hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have h₄ : H[G | pair V Z ; μ] = 0 :=
    (condEntropy_eq_zero_iff hμ _ _).2 ⟨φ, fun ω _ => by rw [hG]; rfl⟩
  linarith

end Split

section Code

variable {N : ℕ} {α : Fin N → Type*} [∀ j, Fintype (α j)] {γ : Type*} [Fintype γ]
  {r : ℕ} {spk : Fin r → Fin N} {M : Fin r → ℕ} [∀ l, NeZero (M l)] {K n : ℕ}
  {κ : Fin N → Type*} [∀ j, Fintype (κ j)] {p : mLetter α γ → ℝ} {θ : ∀ j, κ j → ℝ}

/-- The observation of the node `j`, from a part of the block that contains `j` and from `Zⁿ`. -/
def recObs (d : ∀ j, α j) (d' : ∀ j, κ j) (j : Fin N)
    (v : ((Fin n → ∀ j, Option (α j)) × ∀ j, Option (κ j)) × (Fin n → γ)) : mObs α γ κ n j :=
  (fun i => (v.1.1 i j).getD (d j), v.2, (v.1.2 j).getD (d' j))

omit [(j : Fin N) → Fintype (α j)] [Fintype γ] [(j : Fin N) → Fintype (κ j)] in
lemma recObs_viewB (d : ∀ j, α j) (d' : ∀ j, κ j) {D : Finset (Fin N)} {j : Fin N} (hj : j ∈ D)
    (w : mBlock α γ κ n) : recObs d d' j (viewB D w, eveM w) = nodeObs j w := by
  simp only [recObs, viewB, maskL, hj, ite_true, Option.getD_some, nodeObs]
  rfl

variable (c : MultiKeyCode spk M K (mObs α γ κ n))

/-- The numbers `H(M_l | M^{l-1}, Zⁿ)`. -/
def MultiKeyCode.roundH (μ : mBlock α γ κ n → ℝ) (l : Fin r) : ℝ :=
  H[fun w => c.protocolB w l (runTo (c.protocolB w) l) |
    pair (fun w => runTo (c.protocolB w) l) eveM ; μ]

/-- The sum of the numbers `H(M_l | M^{l-1}, Zⁿ)` over the rounds of the node `j`. -/
def MultiKeyCode.nodeA (μ : mBlock α γ κ n → ℝ) (j : Fin N) : ℝ :=
  ∑ l, if spk l = j then c.roundH μ l else 0

/-- The number `H(Aⱼ | A^{j-1}, Mᵠ, K, Zⁿ)`. -/
def MultiKeyCode.nodeB (μ : mBlock α γ κ n → ℝ) (k₀ j : Fin N) : ℝ :=
  H[partB j | pair (viewB (univ.filter (· < j))) (pair (pair c.transB (c.keyB k₀)) eveM) ; μ]

/-- The bound by Fano's inequality on `H(K₀ | K_k)`. -/
def MultiKeyCode.fanoTerm (μ : mBlock α γ κ n → ℝ) : ℝ :=
  log 2 + c.errProbB μ * log K

/-- **Page 23-56 of [elgamal2010]: the decomposition, for a part `S` of the nodes.**
`H(A(S) | A(Sᶜ), Zⁿ) = H(Mᵠ | D) + H(K | Mᵠ, D) + H(A(S) | Mᵠ, K, D)`, with `D = (A(Sᶜ), Zⁿ)`. -/
lemma MultiKeyCode.condEntropy_viewB_split {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ) (d : ∀ j, α j)
    (d' : ∀ j, κ j) (k₀ : Fin N) (S : Finset (Fin N)) :
    H[viewB S | pair (viewB Sᶜ) eveM ; μ] = H[c.transB | pair (viewB Sᶜ) eveM ; μ] +
      H[c.keyB k₀ | pair c.transB (pair (viewB Sᶜ) eveM) ; μ] +
      H[viewB S | pair (pair c.transB (c.keyB k₀)) (pair (viewB Sᶜ) eveM) ; μ] := by
  classical
  have hU : ∀ w : mBlock α γ κ n, (unionMaskB S (viewB S w) (viewB Sᶜ w), eveM w) =
      (viewB univ w, eveM w) := fun w => by
    refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) rfl
    · simp only [unionMaskB, viewB]
      rw [unionMask_maskL, union_compl]
    · simp only [unionMaskB, viewB]
      rw [unionMask_maskL, union_compl]
  have hT : ∀ w : mBlock α γ κ n, c.transB w =
      run fun l h => c.enc l (recObs d d' (spk l) (unionMaskB S (viewB S w) (viewB Sᶜ w), eveM w))
        h :=
    fun w => by
      simp only [MultiKeyCode.transB]
      congr 1
      funext l h
      rw [hU, recObs_viewB d d' (mem_univ _)]
      rfl
  have hK : ∀ w : mBlock α γ κ n, c.keyB k₀ w =
      c.key k₀ (recObs d d' k₀ (unionMaskB S (viewB S w) (viewB Sᶜ w), eveM w)) (c.transB w) :=
    fun w => by
      simp only [MultiKeyCode.keyB]
      rw [hU, recObs_viewB d d' (mem_univ _)]
  have h₁ := condEntropy_split hμ (viewB S) (pair c.transB (c.keyB k₀)) (pair (viewB Sᶜ) eveM)
    (fun v => (run fun l h => c.enc l (recObs d d' (spk l) (unionMaskB S v.1 v.2.1, v.2.2)) h,
      c.key k₀ (recObs d d' k₀ (unionMaskB S v.1 v.2.1, v.2.2))
        (run fun l h => c.enc l (recObs d d' (spk l) (unionMaskB S v.1 v.2.1, v.2.2)) h)))
    (by
      funext w
      refine Prod.ext (hT w) ?_
      change c.keyB k₀ w = _
      rw [hK, hT w]
      rfl)
  rw [h₁, chain_rule_cond hμ]

/-- `H(X | D', C)` with a constant `D'` is `H(X | C)`. -/
lemma condEntropy_pair_viewB_empty {Ω' a' : Type*} [Fintype Ω'] [Fintype a']
  {μ : mBlock α γ κ n → ℝ}
    (hμ : IsPMF μ) (X : mBlock α γ κ n → a') (C : mBlock α γ κ n → Ω') :
    H[X | pair (viewB ∅) C ; μ] = H[X | C ; μ] := by
  refine condEntropy_eq_of_comp hμ X (fun v => v.2)
    (fun v => ((fun _ _ => none, fun _ => none), v)) rfl ?_
  funext w
  refine Prod.ext (Prod.ext (funext fun i => funext fun j => ?_) (funext fun j => ?_)) rfl <;>
    simp [viewB, maskL]

/-- `H(X | A, D', C)` with a constant `D'` is `H(X | A, C)`. -/
lemma condEntropy_pair_viewB_empty' {Ω' a' b' : Type*} [Fintype Ω'] [Fintype a'] [Fintype b']
    {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ) (X : mBlock α γ κ n → a') (A : mBlock α γ κ n → b')
    (C : mBlock α γ κ n → Ω') : H[X | pair A (pair (viewB ∅) C) ; μ] = H[X | pair A C ; μ] := by
  refine condEntropy_eq_of_comp hμ X (fun v => (v.1, v.2.2))
    (fun v => (v.1, (fun _ _ => none, fun _ => none), v.2)) rfl ?_
  funext w
  refine Prod.ext rfl (Prod.ext (Prod.ext (funext fun i => funext fun j => ?_)
    (funext fun j => ?_)) rfl) <;> simp [viewB, maskL]

/-- **Page 23-57 of [elgamal2010].** The chain of the indices: for `S = [1 : N]`, the indices have
`H(Mᵠ | Zⁿ) = ∑ⱼ aⱼ`. -/
lemma MultiKeyCode.condEntropy_trans_eq_sum {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ) :
    H[c.transB | eveM ; μ] = ∑ j, c.nodeA μ j := by
  classical
  have h := condEntropy_runTo hμ c.protocolB eveM r le_rfl
  have e : ∀ l : Fin r, ((l : ℕ) < r) := fun l => l.isLt
  simp only [e, ite_true] at h
  have hT : (fun w => runTo (c.protocolB w) r) = c.transB := rfl
  rw [hT] at h
  rw [h]
  simp only [MultiKeyCode.nodeA]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  simp [MultiKeyCode.roundH]

/-- **Page 23-58 of [elgamal2010].** For a part `S`, `H(Mᵠ | A(Sᶜ), Zⁿ) ≤ ∑_{j ∈ S} aⱼ`: the indices
of the nodes off `S` are known from the indices before them. -/
lemma MultiKeyCode.condEntropy_trans_le_sum {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ) (d : ∀ j, α j)
    (d' : ∀ j, κ j) (S : Finset (Fin N)) :
    H[c.transB | pair (viewB Sᶜ) eveM ; μ] ≤ ∑ j ∈ S, c.nodeA μ j := by
  classical
  have h := condEntropy_runTo hμ c.protocolB (pair (viewB Sᶜ) eveM) r le_rfl
  have e : ∀ l : Fin r, ((l : ℕ) < r) := fun l => l.isLt
  simp only [e, ite_true] at h
  have hT : (fun w => runTo (c.protocolB w) r) = c.transB := rfl
  rw [hT] at h
  rw [h]
  have hR : ∑ j ∈ S, c.nodeA μ j = ∑ l, if spk l ∈ S then c.roundH μ l else 0 := by
    simp only [MultiKeyCode.nodeA]
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    exact sum_ite_eq S (spk l) _
  rw [hR]
  refine sum_le_sum fun l _ => ?_
  by_cases hl : spk l ∈ S
  · simp only [hl, ite_true, MultiKeyCode.roundH]
    exact condEntropy_le_condEntropy_comp hμ _
      (pair (fun w => runTo (c.protocolB w) l) (pair (viewB Sᶜ) eveM)) fun v => (v.1, v.2.2)
  · simp only [hl, ite_false]
    have hl' : spk l ∈ Sᶜ := by simpa using hl
    refine le_of_eq ((condEntropy_eq_zero_iff hμ _ _).2 ⟨fun v => c.enc l
      (recObs d d' (spk l) (v.2.1, v.2.2)) v.1, fun w _ => ?_⟩)
    simp only [pair]
    rw [recObs_viewB d d' hl']
    rfl

/-- **Page 23-58 of [elgamal2010].** The last term: `H(A(S) | Mᵠ, K, A(Sᶜ), Zⁿ) ≤ ∑_{j ∈ S} bⱼ`. -/
lemma MultiKeyCode.condEntropy_view_le_sum {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ) (d : ∀ j, α j)
    (d' : ∀ j, κ j) (k₀ : Fin N) (S : Finset (Fin N)) :
    H[viewB S | pair (pair c.transB (c.keyB k₀)) (pair (viewB Sᶜ) eveM) ; μ] ≤
      ∑ j ∈ S, c.nodeB μ k₀ j := by
  classical
  set C₀ := pair (pair c.transB (c.keyB k₀)) eveM with hC₀
  have e₁ : H[viewB S | pair (pair c.transB (c.keyB k₀)) (pair (viewB Sᶜ) eveM) ; μ] =
      H[viewB S | pair (viewB Sᶜ) C₀ ; μ] :=
    condEntropy_congr_right hμ (viewB S) (X := pair (viewB Sᶜ) C₀)
      (X' := pair (pair c.transB (c.keyB k₀)) (pair (viewB Sᶜ) eveM))
      (fun v => (v.2.1, v.1, v.2.2))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.1 h.2.2)) fun _ => rfl
  rw [e₁, condEntropy_viewB_eq_sum hμ d d']
  refine sum_le_sum fun j hj => ?_
  simp only [MultiKeyCode.nodeB]
  have hsub : (univ.filter (· < j)) ⊆ (S.filter (· < j)) ∪ Sᶜ := fun x hx => by
    have hx' := (mem_filter.1 hx).2
    by_cases hxS : x ∈ S
    · exact mem_union_left _ (mem_filter.2 ⟨hxS, hx'⟩)
    · exact mem_union_right _ (by simpa using hxS)
  refine (condEntropy_le_condEntropy_comp hμ _ (pair (viewB ((S.filter (· < j)) ∪ Sᶜ)) C₀)
    (fun v => ((fun i => restrictMask (univ.filter (· < j)) (v.1.1 i),
      restrictMask (univ.filter (· < j)) v.1.2), v.2))).trans (le_of_eq ?_)
  refine congrArg _ ?_
  funext w
  refine Prod.ext (Prod.ext (funext fun i => ?_) ?_) rfl
  · exact restrictMask_maskL hsub _
  · exact restrictMask_maskL hsub _

/-- For `S = [1 : N]`, the last term is the sum of the `bⱼ`. -/
lemma MultiKeyCode.condEntropy_view_univ {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ) (d : ∀ j, α j)
    (d' : ∀ j, κ j) (k₀ : Fin N) :
    H[viewB univ | pair (pair c.transB (c.keyB k₀)) eveM ; μ] = ∑ j, c.nodeB μ k₀ j := by
  classical
  have h₁ := condEntropy_viewB_eq_sum hμ d d' ∅ (pair (pair c.transB (c.keyB k₀)) eveM) univ
  rw [condEntropy_pair_viewB_empty hμ] at h₁
  rw [h₁]
  refine sum_congr rfl fun j _ => ?_
  rw [union_empty]
  rfl

/-- The probability that two keys differ is at most the probability of error. -/
lemma MultiKeyCode.errProb_key_le {μ : mBlock α γ κ n → ℝ} (hμ : IsPMF μ) (k₀ k : Fin N) :
    InfoTheory.errProb μ (c.keyB k₀) (c.keyB k) id ≤ c.errProbB μ := by
  classical
  simp only [InfoTheory.errProb, id, MultiKeyCode.errProbB]
  refine sum_le_sum fun w _ => ?_
  have h₀ := hμ.nonneg w
  by_cases h : c.keyB k w = c.keyB k₀ w
  · simp only [h, ne_eq, not_true_eq_false, ite_false]
    split_ifs <;> simp [h₀]
  · have hex : ∃ j j', c.keyB j w ≠ c.keyB j' w := ⟨k, k₀, h⟩
    simp only [hex, ite_true, mul_one]
    split_ifs <;> simp

/-- **Pages 23-57 and 23-58 of [elgamal2010]: the rates are in the region.** For a proper subset
`S`, `n H(X(S) | X(Sᶜ), Z) + ∑_{j ∈ S} H(Wⱼ) ≤ ∑_{j ∈ S} (aⱼ + bⱼ) + η`. -/
theorem MultiKeyCode.mul_zCondH_le (hp : IsPMF p) (hθ : ∀ j, IsPMF (θ j)) (d : ∀ j, α j)
    (d' : ∀ j, κ j) (k₀ : Fin N) {S : Finset (Fin N)} (hS : S ≠ univ) :
    n * zCondH p S + ∑ j ∈ S, entropy (θ j) ≤
      ∑ j ∈ S, c.nodeA (secBlockLaw p (seedsLaw θ) n) j +
        c.fanoTerm (secBlockLaw p (seedsLaw θ) n) +
        ∑ j ∈ S, c.nodeB (secBlockLaw p (seedsLaw θ) n) k₀ j := by
  classical
  have hμ : IsPMF (secBlockLaw p (seedsLaw θ) n) := secBlockLaw_isPMF hp (seedsLaw_isPMF hθ) n
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (univ : Finset (Fin N)), k ∉ S := by
    by_contra h
    push Not at h
    exact hS (eq_univ_of_forall fun j => h j (mem_univ j))
  have hk' : k ∈ Sᶜ := by simpa using hk
  have h₁ := condEntropy_viewB_compl (n := n) hp hθ S
  rw [c.condEntropy_viewB_split hμ d d' k₀ S] at h₁
  have h₂ := c.condEntropy_trans_le_sum hμ d d' S
  have h₃ := c.condEntropy_view_le_sum hμ d d' k₀ S
  -- The key of a node off `S`.
  have h₄ : H[c.keyB k₀ | pair c.transB (pair (viewB Sᶜ) eveM) ; secBlockLaw p (seedsLaw θ) n] ≤
      H[c.keyB k₀ | c.keyB k ; secBlockLaw p (seedsLaw θ) n] := by
    have e := condEntropy_le_condEntropy_comp hμ (c.keyB k₀)
      (pair c.transB (pair (viewB Sᶜ) eveM)) fun v => c.key k (recObs d d' k (v.2.1, v.2.2)) v.1
    refine e.trans (le_of_eq ?_)
    refine congrArg _ ?_
    funext w
    simp only [Function.comp, pair, MultiKeyCode.keyB]
    rw [recObs_viewB d d' hk']
  have h₅ := fano_weak hμ (c.keyB k₀) (c.keyB k) id
  rw [Fintype.card_fin] at h₅
  have h₆ : InfoTheory.errProb (secBlockLaw p (seedsLaw θ) n) (c.keyB k₀) (c.keyB k) id *
      log K ≤ c.errProbB (secBlockLaw p (seedsLaw θ) n) * log K :=
    mul_le_mul_of_nonneg_right (c.errProb_key_le hμ k₀ k) (log_natCast_nonneg _)
  simp only [MultiKeyCode.fanoTerm]
  linarith

/-- **Page 23-56 of [elgamal2010]: the identity for all the nodes.** -/
theorem MultiKeyCode.mul_entropy_eq (hp : IsPMF p) (hθ : ∀ j, IsPMF (θ j)) (d : ∀ j, α j)
    (d' : ∀ j, κ j) (k₀ : Fin N) :
    n * zCondH p univ + ∑ j, entropy (θ j) =
      ∑ j, c.nodeA (secBlockLaw p (seedsLaw θ) n) j +
        H[c.keyB k₀ | pair c.transB eveM ; secBlockLaw p (seedsLaw θ) n] +
        ∑ j, c.nodeB (secBlockLaw p (seedsLaw θ) n) k₀ j := by
  classical
  have hμ : IsPMF (secBlockLaw p (seedsLaw θ) n) := secBlockLaw_isPMF hp (seedsLaw_isPMF hθ) n
  have h₁ := condEntropy_viewB_compl (n := n) hp hθ (univ : Finset (Fin N))
  rw [c.condEntropy_viewB_split hμ d d' k₀ univ] at h₁
  rw [compl_univ] at h₁
  rw [← h₁, condEntropy_pair_viewB_empty hμ, c.condEntropy_trans_eq_sum hμ,
    ← c.condEntropy_view_univ hμ d d' k₀, condEntropy_pair_viewB_empty' hμ,
    condEntropy_pair_viewB_empty' hμ]

/-- **Page 23-57 of [elgamal2010]: the rate of the key.** For `n > 0` and `N ≥ 2`,
`H(K) ≤ n H(X^N | Z) - n R_CFO + N η + I(K; Zⁿ, Mᵠ)`, in nats. -/
theorem MultiKeyCode.entropy_key_le (hp : IsPMF p) (hθ : ∀ j, IsPMF (θ j)) (hn : 0 < n)
    (hN : 2 ≤ N) (k₀ : Fin N) :
    H[c.keyB k₀ ; secBlockLaw p (seedsLaw θ) n] ≤
      n * zCondH p univ - n * log 2 * rCFOZ p + N * c.fanoTerm (secBlockLaw p (seedsLaw θ) n) +
        I[c.keyB k₀ : pair eveM c.transB ; secBlockLaw p (seedsLaw θ) n] := by
  classical
  have hl := log_pos one_lt_two
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ : IsPMF (secBlockLaw p (seedsLaw θ) n) := secBlockLaw_isPMF hp (seedsLaw_isPMF hθ) n
  obtain ⟨a₀⟩ : Nonempty (mLetter α γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  obtain ⟨d'⟩ : Nonempty (∀ j, κ j) :=
    Fintype.card_pos_iff.1 (card_pos_of_isPMF (seedsLaw_isPMF hθ))
  set d := a₀.1
  set μ := secBlockLaw p (seedsLaw θ) n with hμd
  set η := c.fanoTerm μ with hη
  have herr0 : 0 ≤ c.errProbB μ := sum_nonneg fun w _ => mul_nonneg (hμ.nonneg w) (by
    split_ifs <;> norm_num)
  have hη0 : 0 ≤ η := by
    have h₁ : 0 ≤ log (K : ℝ) := log_natCast_nonneg _
    have h₂ := mul_nonneg herr0 h₁
    simp only [hη, MultiKeyCode.fanoTerm]
    linarith
  set ra : Fin N → ℝ := fun j => c.nodeA μ j + c.nodeB μ k₀ j - entropy (θ j) with hra
  have hreg : ∀ S : Finset (Fin N), S ≠ univ → n * zCondH p S ≤ ∑ j ∈ S, ra j + η := fun S hS => by
    have h := c.mul_zCondH_le hp hθ d d' k₀ hS
    simp only [hra, sum_sub_distrib, sum_add_distrib]
    linarith
  set Rt : Fin N → ℝ := fun j => (ra j + η) / (n * log 2) with hRt
  have hpos : 0 < (n : ℝ) * log 2 := mul_pos hn0 hl
  have hzero : zCondH p ∅ = 0 := by
    refine (condEntropy_eq_zero_iff hp _ _).2 ⟨fun _ _ => none, fun a _ => ?_⟩
    exact maskL_empty a.1
  have hRt0 : ∀ j, 0 ≤ Rt j := fun j => by
    refine div_nonneg ?_ hpos.le
    have hS : ({j} : Finset (Fin N)) ≠ univ := fun h => by
      have hcard : (({j} : Finset (Fin N)).card) = N := by
        rw [h, card_univ, Fintype.card_fin]
      simp at hcard
      omega
    have h := hreg {j} hS
    rw [sum_singleton] at h
    have h₀ : 0 ≤ (n : ℝ) * zCondH p {j} := mul_nonneg hn0.le (condEntropy_nonneg hp _ _)
    linarith
  have hmem : Rt ∈ zRegion p := by
    refine ⟨hRt0, fun S hS => ?_⟩
    rw [div_le_iff₀ hl]
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [hzero]
    · have h := hreg S hS
      have hsum : (∑ j ∈ S, Rt j) * log 2 = (∑ j ∈ S, (ra j + η)) / n := by
        simp only [hRt, sum_div]
        rw [sum_mul]
        refine sum_congr rfl fun j _ => ?_
        field_simp
      rw [hsum, le_div_iff₀ hn0, sum_add_distrib, sum_const, nsmul_eq_mul]
      have hc : (1 : ℝ) ≤ S.card := by exact_mod_cast hne.card_pos
      have : η ≤ S.card * η := by nlinarith
      nlinarith
  have hbdd : BddBelow ((fun R : Fin N → ℝ => ∑ j, R j) '' zRegion p) :=
    ⟨0, by
      rintro _ ⟨R, hR, rfl⟩
      exact sum_nonneg fun j _ => hR.1 j⟩
  have hcfo : rCFOZ p ≤ ∑ j, Rt j := csInf_le hbdd ⟨Rt, hmem, rfl⟩
  have hsumR : n * log 2 * ∑ j, Rt j = ∑ j, ra j + N * η := by
    simp only [hRt, mul_sum]
    have : ∀ j, (n : ℝ) * log 2 * ((ra j + η) / (n * log 2)) = ra j + η := fun j => by
      field_simp
    simp only [this, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hid := c.mul_entropy_eq hp hθ d d' k₀
  have hle : n * log 2 * rCFOZ p ≤ n * log 2 * ∑ j, Rt j := mul_le_mul_of_nonneg_left hcfo hpos.le
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ (c.keyB k₀) (pair eveM c.transB)
  have hswap : H[c.keyB k₀ | pair eveM c.transB ; μ] = H[c.keyB k₀ | pair c.transB eveM ; μ] :=
    condEntropy_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl
  have hsra : ∑ j, ra j = ∑ j, c.nodeA μ j + ∑ j, c.nodeB μ k₀ j - ∑ j, entropy (θ j) := by
    simp only [hra, sum_sub_distrib, sum_add_distrib]
  linarith

/-- **Pages 23-56 to 23-59 of [elgamal2010]: the converse of Theorem 9.** For `N ≥ 2`, an achievable
rate is at most `H(X^N | Z) - R_CFO([1 : N] | Z)`, in bits. -/
theorem IsAchievableMultiKey.le (hp : IsPMF p) (hN : 2 ≤ N) {R : ℝ}
    (h : IsAchievableMultiKey p R) : R ≤ zCondH p univ / log 2 - rCFOZ p := by
  have hl := log_pos one_lt_two
  have ha : 0 ≤ R * log 2 := mul_nonneg h.1 hl.le
  have hk₀ : 0 < N := by omega
  have key : R * log 2 ≤ zCondH p univ - log 2 * rCFOZ p := by
    refine le_of_forall_eventually_mul_le ha fun ε' hε' => ?_
    refine ⟨2 * N * log 2, ?_⟩
    set ε := min 1 (ε' / (2 * (N + 1))) with hε
    have hε0 : 0 < ε := lt_min one_pos (by positivity)
    have hε₁ : ε ≤ 1 := min_le_left _ _
    have hε₂ : ε * (2 * (N + 1)) ≤ ε' := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    filter_upwards [h.2 ε hε0, eventually_gt_atTop 0] with n hn hn1
    obtain ⟨r, spk, M, hM, κ, _, θ, c, hθ, herr, hl₁, hk₁⟩ := hn
    have hb := c.entropy_key_le hp hθ hn1 hN ⟨0, hk₀⟩
    have h₁ := hl₁ ⟨0, hk₀⟩
    have h₂ := hk₁ ⟨0, hk₀⟩
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlogK := log_two_pow_ceil_le n h.1
    have hlogK0 : 0 ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := log_natCast_nonneg _
    have h₃ : c.fanoTerm (secBlockLaw p (seedsLaw θ) n) ≤ log 2 + ε * (n * (R * log 2) + log 2) :=
      by
      simp only [MultiKeyCode.fanoTerm]
      have := (mul_le_mul_of_nonneg_right herr hlogK0).trans
        (mul_le_mul_of_nonneg_left hlogK hε0.le)
      linarith
    have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h₄ := mul_le_mul_of_nonneg_left h₃ hNR
    have hA : 0 ≤ (n : ℝ) * (R * log 2) := mul_nonneg hn0 ha
    have h₅ : ε * log 2 ≤ log 2 := by nlinarith
    have h₆ : (N : ℝ) * (ε * log 2) ≤ N * log 2 := mul_le_mul_of_nonneg_left h₅ hNR
    have h₇ : (N : ℝ) * ε * ((n : ℝ) * (R * log 2)) ≤ ε' * (n * (R * log 2)) := by
      refine mul_le_mul_of_nonneg_right ?_ hA
      nlinarith
    have h₈ : (n : ℝ) * (2 * ε) ≤ n * ε' := by
      refine mul_le_mul_of_nonneg_left ?_ hn0
      nlinarith
    have e₁ : (n : ℝ) * (R * log 2 - ε) = n * (R * log 2) - n * ε := by ring
    have e₂ : (n : ℝ) * (zCondH p univ - log 2 * rCFOZ p + ε') =
        n * zCondH p univ - n * log 2 * rCFOZ p + n * ε' := by ring
    have e₃ : (1 - ε') * ((n : ℝ) * (R * log 2)) = n * (R * log 2) - ε' * (n * (R * log 2)) :=
      by ring
    have e₄ : (N : ℝ) * (log 2 + ε * (n * (R * log 2) + log 2)) =
        N * log 2 + N * ε * (n * (R * log 2)) + N * (ε * log 2) := by ring
    have e₅ : (n : ℝ) * (2 * ε) = n * ε + n * ε := by ring
    have e₆ : 2 * (N : ℝ) * log 2 = N * log 2 + N * log 2 := by ring
    rw [e₂, e₃, e₆]
    linarith
  have hd : zCondH p univ / log 2 - rCFOZ p = (zCondH p univ - log 2 * rCFOZ p) / log 2 := by
    field_simp
  rw [hd, le_div_iff₀ hl]
  exact key

end Code

end InfoTheory
