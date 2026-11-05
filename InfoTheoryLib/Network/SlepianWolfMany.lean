/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.SlepianWolfBits
public import InfoTheoryLib.Typicality.Conditional

/-!
# The Slepian–Wolf theorem for more than two sources

Theorem 3 of Lecture 11: the optimal rate region of a `k`-DMS `(X₁, …, X_k)` is the set of rate
tuples
with `∑_{j ∈ S} Rⱼ ≥ H(X(S) | X(Sᶜ))` for all `S ⊆ [1 : k]`.

The converse is Fano's inequality for each `S`. For achievability each sequence of each source is
put
in a random bin, and a wrong sequence `x'` is split according to the set `S` of the sources where it
differs from the right one: it falls in the right bins with probability `∏_{j ∈ S} 1/Mⱼ`, and there
are at most `e^{n(H(X(S) | X(Sᶜ)) + δ)}` typical such sequences.

## Main definitions

* `ManyCode M n α`: a distributed source code with `M j` indices for the source `j`.
* `swPart S x`, `swRest S x`: the coordinates of `x` in `S` and off `S`.
* `swCondH q S`: `H(X(S) | X(Sᶜ))`, in nats.
* `IsAchievableManyBits q R`, `manyOptimalRegionBits q`, `manyRegionBits q`.

## Main statements

* `ManyCode.mul_swCondH_le`: the converse for one code.
* `exists_many_code_le`: the random binning bound.
* `manyOptimalRegionBits_eq`: **Theorem 3 of Lecture 11**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 11
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]

/-- **Theorem 3 of Lecture 11 of [elgamal2010], page 11-32.** A distributed source code for `k`
sources: an encoder for each source and a decoder of all of them. -/
structure ManyCode (M : ι → ℕ) (n : ℕ) (α : ι → Type*) where
  /-- The encoder of the source `j`. -/
  enc : ∀ j, (Fin n → α j) → Fin (M j)
  /-- The decoder. -/
  dec : (∀ j, Fin (M j)) → Fin n → ∀ j, α j

/-- The indices of all the encoders. -/
def ManyCode.index {M : ι → ℕ} {n : ℕ} (c : ManyCode M n α) (ω : Fin n → ∀ j, α j) (j : ι) :
    Fin (M j) :=
  c.enc j fun i => ω i j

/-- The probability of error `P{X̂ⁿ ≠ Xⁿ}` of a code. -/
def ManyCode.errProb {M : ι → ℕ} {n : ℕ} (c : ManyCode M n α) (q : (∀ j, α j) → ℝ) : ℝ :=
  InfoTheory.errProb (iidPMF q n) id c.index c.dec

/-- The coordinates in `S`. -/
def swPart (S : Finset ι) (x : ∀ j, α j) : ∀ j : S, α j := fun j => x j

/-- The coordinates off `S`. -/
def swRest (S : Finset ι) (x : ∀ j, α j) : ∀ j : {j // j ∉ S}, α j := fun j => x j

omit [Fintype ι] [DecidableEq ι] [∀ j, Fintype (α j)] in
private lemma pair_swRest_swPart_injective (S : Finset ι) :
    Function.Injective fun x : ∀ j, α j => (swRest S x, swPart S x) := fun x y h => by
  funext j
  by_cases hj : j ∈ S
  · exact congrFun (Prod.mk.inj h).2 ⟨j, hj⟩
  · exact congrFun (Prod.mk.inj h).1 ⟨j, hj⟩

/-- **Theorem 3 of Lecture 11.** `H(X(S) | X(Sᶜ))`, in nats. -/
def swCondH (q : (∀ j, α j) → ℝ) (S : Finset ι) : ℝ := H[swPart S | swRest S ; q]

/-- **Theorem 3 of Lecture 11.** A rate tuple, in bits, is achievable if there are codes with the
index sets `[1 : 2^{nRⱼ})` whose probability of error tends to `0`. -/
def IsAchievableManyBits (q : (∀ j, α j) → ℝ) (R : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ R j) ∧ ∃ c : ∀ n : ℕ, ManyCode (fun j => 2 ^ ⌊n * R j⌋₊) n α,
    Tendsto (fun n => (c n).errProb q) atTop (𝓝 0)

/-- **Theorem 3 of Lecture 11.** The optimal rate region. -/
def manyOptimalRegionBits (q : (∀ j, α j) → ℝ) : Set (ι → ℝ) :=
  closure {R | IsAchievableManyBits q R}

/-- **Theorem 3 of Lecture 11 of [elgamal2010], page 11-32, the region.**
`∑_{j ∈ S} Rⱼ ≥ H(X(S) | X(Sᶜ))` for all `S`, in bits. -/
def manyRegionBits (q : (∀ j, α j) → ℝ) : Set (ι → ℝ) :=
  {R | ∀ S : Finset ι, swCondH q S / log 2 ≤ ∑ j ∈ S, R j}

lemma isClosed_manyRegionBits (q : (∀ j, α j) → ℝ) : IsClosed (manyRegionBits q) := by
  simp only [manyRegionBits, Set.ofPred_forall]
  exact isClosed_iInter fun S => isClosed_le continuous_const
    (continuous_finsetSum _ fun j _ => continuous_apply j)

/-! ### Laws of i.i.d. sequences -/

section Iid

variable {γ τ : Type*} [Fintype γ] [Fintype τ]

omit [Fintype τ] in
/-- A function applied letter by letter to an i.i.d. sequence is i.i.d. -/
lemma dist_iidPMF_comp (p : γ → ℝ) (n : ℕ) (f : γ → τ) :
    dist (iidPMF p n) (fun ω i => f (ω i)) = iidPMF (dist p f) n := by
  classical
  funext v
  simp only [dist, iidPMF]
  refine Eq.trans (sum_congr rfl fun ω _ => ?_)
    (Fintype.prod_sum fun i a => if f a = v i then p a else 0).symm
  by_cases h : ∀ i, f (ω i) = v i
  · have e2 : ∏ i, (if f (ω i) = v i then p (ω i) else 0) = ∏ i, p (ω i) :=
      prod_congr rfl fun i _ => by simp [h i]
    rw [e2]
    split_ifs with h3
    · rfl
    · exact absurd (funext h) h3
  · obtain ⟨i, hi⟩ := not_forall.1 h
    have e2 : ∏ i, (if f (ω i) = v i then p (ω i) else 0) = 0 :=
      prod_eq_zero (mem_univ i) (by simp [hi])
    rw [e2]
    split_ifs with h3
    · exact absurd (fun i => congrFun h3 i) h
    · rfl

/-- The entropy of a letter-by-letter function of an i.i.d. sequence. -/
lemma entropyRV_iidPMF_comp {p : γ → ℝ} (hp : IsPMF p) (n : ℕ) (f : γ → τ) :
    H[fun (ω : Fin n → γ) i => f (ω i) ; iidPMF p n] = n * H[f ; p] := by
  rw [entropyRV, dist_iidPMF_comp, entropy_iidPMF (hp.dist f)]
  rfl

end Iid

/-! ### The converse -/

section Converse

variable {q : (∀ j, α j) → ℝ} {M : ι → ℕ} {n : ℕ}

/-- `H(X(S)ⁿ | X(Sᶜ)ⁿ) = n H(X(S) | X(Sᶜ))`. -/
lemma condEntropy_iid_swPart (hq : IsPMF q) (n : ℕ) (S : Finset ι) :
    H[fun (ω : Fin n → ∀ j, α j) i => swPart S (ω i) |
      fun ω i => swRest S (ω i) ; iidPMF q n] = n * swCondH q S := by
  classical
  have hμ := iidPMF_isPMF hq n
  have e1 : H[pair (fun (ω : Fin n → ∀ j, α j) i => swRest S (ω i))
      (fun ω i => swPart S (ω i)) ; iidPMF q n] =
      H[fun (ω : Fin n → ∀ j, α j) i => (swRest S (ω i), swPart S (ω i)) ; iidPMF q n] := by
    refine entropyRV_eq_of_injective _ (fun w => (fun i => (w i).1, fun i => (w i).2)) ?_
      fun _ => rfl
    intro w w' h
    funext i
    exact Prod.ext (congrFun (Prod.mk.inj h).1 i) (congrFun (Prod.mk.inj h).2 i)
  rw [condEntropy_eq_sub hμ, e1, entropyRV_iidPMF_comp hq n (fun x => (swRest S x, swPart S x)),
    entropyRV_iidPMF_comp hq n (swRest S), swCondH, condEntropy_eq_sub hq]
  have e2 : H[pair (swRest S) (swPart S) ; q] = H[fun x => (swRest S x, swPart S x) ; q] := rfl
  rw [e2]
  ring

/-- `H(f(X) | Y) ≤ H(X | Y)`. -/
private lemma condEntropy_comp_le' {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b]
    [Fintype c] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → a) (Y : Ω → b) (f : a → c) :
    H[f ∘ X | Y ; μ] ≤ H[X | Y ; μ] := by
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  have h := entropyRV_comp_le hμ (pair Y X) (Prod.map id f)
  have e : Prod.map id f ∘ pair Y X = pair Y (f ∘ X) := rfl
  rw [e] at h
  linarith

/-- **Theorem 3 of Lecture 11, the converse for one code.** For every `S`,
`n H(X(S) | X(Sᶜ)) ≤ ∑_{j ∈ S} log Mⱼ + log 2 + Pₑ n log |𝒳|`. -/
theorem ManyCode.mul_swCondH_le (c : ManyCode M n α) (hq : IsPMF q) (S : Finset ι)
    (hM : ∀ j, 0 < M j) :
    n * swCondH q S ≤ ∑ j ∈ S, log (M j) + log 2 +
      c.errProb q * (n * log (Fintype.card (∀ j, α j))) := by
  classical
  have hμ := iidPMF_isPMF hq n
  set A : (Fin n → ∀ j, α j) → Fin n → ∀ j : {j // j ∉ S}, α j := fun ω i => swRest S (ω i)
  set B : (Fin n → ∀ j, α j) → Fin n → ∀ j : S, α j := fun ω i => swPart S (ω i)
  set Ms : (Fin n → ∀ j, α j) → ∀ j : S, Fin (M j) := fun ω j => c.index ω j
  have hn := condEntropy_iid_swPart hq n S
  rw [← hn]
  -- `H(B | A) ≤ H(Ms | A) + H(B | Ms, A)`.
  have hc1 := chain_rule_cond hμ B Ms A
  have hc2 := chain_rule_cond hμ Ms B A
  have hswap : H[pair B Ms | A ; iidPMF q n] = H[pair Ms B | A ; iidPMF q n] :=
    condEntropy_congr_left hμ A Prod.swap Prod.swap_injective fun _ => rfl
  have h0 := condEntropy_nonneg hμ Ms (pair B A)
  -- `H(Ms | A) ≤ ∑_{j ∈ S} log Mⱼ`.
  have hMs : H[Ms | A ; iidPMF q n] ≤ ∑ j ∈ S, log (M j) := by
    refine (condEntropy_le_entropy hμ Ms A).trans
      ((entropyRV_le_log_card hμ Ms).trans (le_of_eq ?_))
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    push_cast
    rw [log_prod fun j _ => by exact_mod_cast (hM j).ne']
    exact sum_coe_sort S fun j => log (M j)
  -- The indices are determined by `Ms` and `A`.
  have hdet := condEntropy_le_condEntropy_comp hμ B (pair Ms A)
    (fun w j => if hj : j ∈ S then w.1 ⟨j, hj⟩ else c.enc j fun i => w.2 i ⟨j, hj⟩)
  have hdete : (fun (w : (∀ j : S, Fin (M j)) × (Fin n → ∀ j : {j // j ∉ S}, α j)) (j : ι) =>
      if hj : j ∈ S then w.1 ⟨j, hj⟩ else c.enc j fun i => w.2 i ⟨j, hj⟩) ∘ pair Ms A =
      c.index := by
    funext ω j
    by_cases hj : j ∈ S
    · simp [pair, Ms, hj]
    · simp [pair, A, swRest, hj, ManyCode.index]
  rw [hdete] at hdet
  have hle := condEntropy_comp_le' hμ (id : (Fin n → ∀ j, α j) → _) c.index
    (fun ω i => swPart S (ω i))
  have hB : (fun (ω : Fin n → ∀ j, α j) i => swPart S (ω i)) ∘ id = B := rfl
  rw [hB] at hle
  have hfano := fano_weak hμ (id : (Fin n → ∀ j, α j) → _) c.index c.dec
  have hcard : log (Fintype.card (Fin n → ∀ j, α j)) = n * log (Fintype.card (∀ j, α j)) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  rw [hcard] at hfano
  have herr : c.errProb q = InfoTheory.errProb (iidPMF q n) id c.index c.dec := rfl
  rw [herr]
  linarith

/-- **Theorem 3 of Lecture 11, the converse.** -/
theorem IsAchievableManyBits.mem_manyRegionBits (hq : IsPMF q) {R : ι → ℝ}
    (h : IsAchievableManyBits q R) : R ∈ manyRegionBits q := by
  obtain ⟨hR, c, hc⟩ := h
  intro S
  have hl := log_pos one_lt_two
  refine (div_le_iff₀ hl).2 ?_
  rw [sum_mul]
  refine le_of_sw_bound (L := log (Fintype.card (∀ j, α j))) hc fun n _ => ?_
  have h1 := (c n).mul_swCondH_le hq S fun j => by positivity
  have h2 : ∑ j ∈ S, log (((2 ^ ⌊n * R j⌋₊ : ℕ) : ℝ)) ≤ n * ∑ j ∈ S, R j * log 2 := by
    rw [mul_sum]
    exact sum_le_sum fun j _ => log_two_pow_floor_le n (hR j)
  linarith

end Converse

/-! ### Random binning -/

section Binning

variable {q : (∀ j, α j) → ℝ} {M : ι → ℕ} {n : ℕ}

/-- The number of sequences of the source `j`. -/
private abbrev seqN (α : ι → Type*) [∀ j, Fintype (α j)] (n : ℕ) (j : ι) : ℕ :=
  Fintype.card (Fin n → α j)

/-- The law of the bin assignments, independent for each source. -/
private def manyBinLaw (M : ι → ℕ) (n : ℕ) (α : ι → Type*) [∀ j, Fintype (α j)]
    (B : ∀ j, Fin (seqN α n j) → Fin (M j)) : ℝ :=
  ∏ j, iidPMF (uniformPMF (Fin (M j))) (seqN α n j) (B j)

/-- The bin of a sequence of the source `j`. -/
private def manyBin (B : ∀ j, Fin (seqN α n j) → Fin (M j)) (ω : Fin n → ∀ j, α j) (j : ι) :
    Fin (M j) :=
  B j (Fintype.equivFin (Fin n → α j) fun i => ω i j)

/-- The sum over the bin assignments of a product of a function of each. -/
private lemma sum_manyBinLaw_prod
    (g : ∀ j, (Fin (seqN α n j) → Fin (M j)) → ℝ) :
    ∑ B, manyBinLaw M n α B * ∏ j, g j (B j) =
      ∏ j, ∑ Bj, iidPMF (uniformPMF (Fin (M j))) (seqN α n j) Bj * g j Bj := by
  simp only [manyBinLaw, ← prod_mul_distrib]
  exact (Fintype.prod_sum fun j Bj =>
    iidPMF (uniformPMF (Fin (M j))) (seqN α n j) Bj * g j Bj).symm

private lemma manyBinLaw_isPMF (hM : ∀ j, 0 < M j) : IsPMF (manyBinLaw M n α) := by
  have hne : ∀ j, Nonempty (Fin (M j)) := fun j => ⟨⟨0, hM j⟩⟩
  refine ⟨fun B => prod_nonneg fun j _ => iidPMF_nonneg
    (uniformPMF_isPMF (α := Fin (M j))).nonneg _, ?_⟩
  have h := sum_manyBinLaw_prod (M := M) (n := n) (α := α) fun _ _ => 1
  simp only [prod_const_one, mul_one] at h
  rw [h]
  refine prod_eq_one fun j _ => ?_
  exact (iidPMF_isPMF (uniformPMF_isPMF (α := Fin (M j))) _).sum_eq_one

open Classical in
/-- **Theorem 3 of Lecture 11, achievability.** Two different sequences fall in the same bins with
probability `∏_{j ∈ S} 1/Mⱼ`, where `S` is the set of the sources on which they differ. -/
private lemma sum_manyBinLaw_collision (hM : ∀ j, 0 < M j) (ω ω' : Fin n → ∀ j, α j) :
    ∑ B, manyBinLaw M n α B * (if ∀ j, manyBin B ω' j = manyBin B ω j then 1 else 0) =
      ∏ j ∈ univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j, (1 / (M j : ℝ)) := by
  have hne : ∀ j, Nonempty (Fin (M j)) := fun j => ⟨⟨0, hM j⟩⟩
  have e : ∀ B : ∀ j, Fin (seqN α n j) → Fin (M j),
      (if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0) =
        ∏ j, if manyBin B ω' j = manyBin B ω j then 1 else 0 := fun B => by
    by_cases h : ∀ j, manyBin B ω' j = manyBin B ω j
    · simp [h]
    · obtain ⟨j, hj⟩ := not_forall.1 h
      rw [prod_eq_zero (mem_univ j) (by simp [hj])]
      split_ifs
      rfl
  simp only [e]
  refine (sum_manyBinLaw_prod (M := M) (n := n) (α := α) fun j Bj =>
    if Bj (Fintype.equivFin (Fin n → α j) fun i => ω' i j) =
      Bj (Fintype.equivFin (Fin n → α j) fun i => ω i j) then 1 else 0).trans ?_
  rw [prod_filter]
  refine prod_congr rfl fun j _ => ?_
  by_cases hj : (fun i => ω' i j) = fun i => ω i j
  · rw [hj]
    simp only [ne_eq, not_true_eq_false, ite_false, ite_true, mul_one]
    exact (iidPMF_isPMF (uniformPMF_isPMF (α := Fin (M j))) _).sum_eq_one
  · have hne' : Fintype.equivFin (Fin n → α j) (fun i => ω i j) ≠
        Fintype.equivFin (Fin n → α j) fun i => ω' i j := fun h =>
      hj ((Fintype.equivFin _).injective h).symm
    simp only [ne_eq, hj, not_false_eq_true, ite_true]
    exact sum_bins_eq_eq (hM j) hne'

open Classical in
/-- The decoder: the unique typical sequence in the bins, and `d` if there is none. -/
private def manyDec (T : Finset (Fin n → ∀ j, α j)) (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (d : Fin n → ∀ j, α j) (w : ∀ j, Fin (M j)) : Fin n → ∀ j, α j :=
  if h : ∃ x, x ∈ T ∧ (∀ j, manyBin B x j = w j) ∧ ∀ x' ∈ T, (∀ j, manyBin B x' j = w j) → x' = x
  then h.choose else d

open Classical in
private lemma manyDec_ne_le (T : Finset (Fin n → ∀ j, α j)) (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (d ω : Fin n → ∀ j, α j) :
    (if manyDec T B d (manyBin B ω) ≠ ω then (1 : ℝ) else 0) ≤
      (if ω ∉ T then 1 else 0) +
        ∑ ω' ∈ T.erase ω, if ∀ j, manyBin B ω' j = manyBin B ω j then 1 else 0 := by
  have hn0 : (0 : ℝ) ≤ ∑ ω' ∈ T.erase ω,
      if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hx : ω ∈ T
  · by_cases hu : ∀ ω' ∈ T, (∀ j, manyBin B ω' j = manyBin B ω j) → ω' = ω
    · have hex : ∃ x, x ∈ T ∧ (∀ j, manyBin B x j = manyBin B ω j) ∧
          ∀ x' ∈ T, (∀ j, manyBin B x' j = manyBin B ω j) → x' = x :=
        ⟨ω, hx, fun _ => rfl, hu⟩
      have hd : manyDec T B d (manyBin B ω) = ω := by
        simp only [manyDec]
        split
        · rename_i h
          exact hu _ h.choose_spec.1 h.choose_spec.2.1
        · contradiction
      simp only [hd, ne_eq, not_true_eq_false, ite_false, hx, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨ω', hω', hb, hne⟩ := hu
      have h1 : (1 : ℝ) ≤ ∑ ω' ∈ T.erase ω,
          if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0 := by
        have := single_le_sum (f := fun ω' => if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ)
          else 0) (fun _ _ => by split_ifs <;> norm_num) (mem_erase.2 ⟨hne, hω'⟩)
        simpa [hb] using this
      split_ifs <;> linarith
  · simp only [hx, not_false_eq_true, ite_true]
    split_ifs <;> linarith

/-- The joint law of `(X(Sᶜ), X(S))`. -/
private def swJoint (q : (∀ j, α j) → ℝ) (S : Finset ι) :
    (∀ j : {j // j ∉ S}, α j) × (∀ j : S, α j) → ℝ :=
  dist q fun x => (swRest S x, swPart S x)

private lemma swCondH_eq (hq : IsPMF q) (S : Finset ι) :
    swCondH q S = H[Prod.snd | Prod.fst ; swJoint q S] := by
  refine condEntropy_eq_of_dist_pair_eq hq (hq.dist _) ?_
  rw [dist_pair_fst_snd]
  rfl

open Classical in
/-- **Lecture 11, page 11-18, for `k` sources.** The number of typical sequences that differ from
`ω` exactly on the sources in `S`. -/
private lemma card_filter_diff_le (hq : IsPMF q) {ε : ℝ} (ω : Fin n → ∀ j, α j) (S : Finset ι) :
    ((((robustTypicalSet q n ε).erase ω).filter fun ω' =>
      (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S).card : ℝ) ≤
      exp (n * (swCondH q S + ε * swCondH q S)) := by
  have hJ : IsPMF (swJoint q S) := hq.dist _
  have hb := card_condRobustTypicalSet_le hJ ε (fun i => swRest S (ω i))
  rw [← swCondH_eq hq S] at hb
  refine le_trans ?_ hb
  norm_cast
  refine card_le_card_of_injOn (fun ω' i => swPart S (ω' i)) ?_ ?_
  · intro ω' hω'
    have hm := Finset.mem_filter.1 (Finset.mem_coe.1 hω')
    have hT := (mem_erase.1 hm.1).2
    have key : ∀ a : ι, a ∉ S → (fun i => ω' i a) = fun i => ω i a := fun a ha => by
      by_contra hne
      exact ha (by
        rw [← hm.2]
        exact Finset.mem_filter.2 ⟨mem_univ _, hne⟩)
    have hrest : (fun i => swRest S (ω' i)) = fun i => swRest S (ω i) := by
      funext i
      funext j
      exact congrFun (key j j.2) i
    refine Finset.mem_coe.2 (mem_condRobustTypicalSet.2 ?_)
    have h := comp_mem_robustTypicalSet hT fun x => (swRest S x, swPart S x)
    have e : zipSeq (fun i => swRest S (ω i)) (fun i => swPart S (ω' i)) =
        (fun x => (swRest S x, swPart S x)) ∘ ω' := by
      funext i
      exact Prod.ext (congrFun hrest i).symm rfl
    rw [e]
    exact h
  · intro ω' hω' ω'' hω'' he
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 hω')
    have hm'' := Finset.mem_filter.1 (Finset.mem_coe.1 hω'')
    funext i
    funext j
    by_cases hj : j ∈ S
    · exact congrFun (congrFun he i) ⟨j, hj⟩
    · have h1 : (fun i => ω' i j) = fun i => ω i j := by
        by_contra hne
        exact hj (by
          rw [← hm'.2]
          exact Finset.mem_filter.2 ⟨mem_univ _, hne⟩)
      have h2 : (fun i => ω'' i j) = fun i => ω i j := by
        by_contra hne
        exact hj (by
          rw [← hm''.2]
          exact Finset.mem_filter.2 ⟨mem_univ _, hne⟩)
      exact (congrFun h1 i).trans (congrFun h2 i).symm

open Classical in
/-- **Lecture 11, pages 11-17 to 11-19, for `k` sources.** The random binning bound: there is a code
with `Pₑ ≤ P{Xⁿ ∉ T} + ∑_{S ≠ ∅} e^{n(H(X(S) | X(Sᶜ)) + δ)} ∏_{j ∈ S} 1/Mⱼ`. -/
theorem exists_many_code_le (hq : IsPMF q) (hM : ∀ j, 0 < M j) (ε : ℝ) :
    ∃ c : ManyCode M n α, c.errProb q ≤ (1 - prob (iidPMF q n) (robustTypicalSet q n ε)) +
      ∑ S ∈ univ.filter fun S : Finset ι => S.Nonempty,
        exp (n * (swCondH q S + ε * swCondH q S)) * ∏ j ∈ S, (1 / (M j : ℝ)) := by
  have hμ := iidPMF_isPMF hq n
  obtain ⟨z₀⟩ : Nonempty (∀ j, α j) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hq)
  set d : Fin n → ∀ j, α j := fun _ => z₀
  set T := robustTypicalSet q n ε
  have hlaw := manyBinLaw_isPMF (M := M) (n := n) (α := α) hM
  set K := ∑ S ∈ univ.filter fun S : Finset ι => S.Nonempty,
    exp (n * (swCondH q S + ε * swCondH q S)) * ∏ j ∈ S, (1 / (M j : ℝ)) with hKd
  let code : (∀ j, Fin (seqN α n j) → Fin (M j)) → ManyCode M n α := fun B =>
    ⟨fun j x => B j (Fintype.equivFin (Fin n → α j) x), manyDec T B d⟩
  -- The sum of the probabilities of a collision, for a fixed `ω`.
  have hcoll : ∀ ω : Fin n → ∀ j, α j, ∑ ω' ∈ T.erase ω,
      ∏ j ∈ univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j, (1 / (M j : ℝ)) ≤ K :=
      fun ω => by
    have hmaps : ∀ ω' ∈ T.erase ω, (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) ∈
        univ.filter fun S : Finset ι => S.Nonempty := fun ω' hω' => by
      refine Finset.mem_filter.2 ⟨mem_univ _, ?_⟩
      by_contra hne
      refine (mem_erase.1 hω').1 ?_
      funext i
      funext j
      have hj : (fun i => ω' i j) = fun i => ω i j := by
        by_contra h
        exact hne ⟨j, Finset.mem_filter.2 ⟨mem_univ _, h⟩⟩
      exact congrFun hj i
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine sum_le_sum fun S _ => ?_
    have hprod0 : (0 : ℝ) ≤ ∏ j ∈ S, (1 / (M j : ℝ)) := prod_nonneg fun _ _ => by positivity
    calc ∑ ω' ∈ (T.erase ω).filter (fun ω' =>
          (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S),
          ∏ j ∈ univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j, (1 / (M j : ℝ))
        = ∑ ω' ∈ (T.erase ω).filter (fun ω' =>
            (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S),
            ∏ j ∈ S, (1 / (M j : ℝ)) :=
          sum_congr rfl fun ω' hω' => by rw [(Finset.mem_filter.1 hω').2]
      _ = (((T.erase ω).filter (fun ω' =>
            (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S)).card : ℝ) *
            ∏ j ∈ S, (1 / (M j : ℝ)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (card_filter_diff_le hq ω S) hprod0
  -- The average over the binnings.
  have hω : ∀ ω : Fin n → ∀ j, α j, ∑ B, manyBinLaw M n α B *
      (if manyDec T B d (manyBin B ω) ≠ ω then (1 : ℝ) else 0) ≤
      (if ω ∉ T then 1 else 0) + K := fun ω => by
    calc ∑ B, manyBinLaw M n α B * (if manyDec T B d (manyBin B ω) ≠ ω then (1 : ℝ) else 0)
        ≤ ∑ B, manyBinLaw M n α B * ((if ω ∉ T then 1 else 0) +
            ∑ ω' ∈ T.erase ω, if ∀ j, manyBin B ω' j = manyBin B ω j then 1 else 0) :=
          sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (manyDec_ne_le T B d ω) (hlaw.nonneg B)
      _ = (if ω ∉ T then 1 else 0) + ∑ ω' ∈ T.erase ω, ∑ B, manyBinLaw M n α B *
            (if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hlaw.sum_eq_one, one_mul]
          congr 1
          simp only [mul_sum]
          exact sum_comm
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          simp only [sum_manyBinLaw_collision hM]
          exact hcoll ω
  have hsumT : ∑ ω, iidPMF q n ω * (if ω ∉ T then (1 : ℝ) else 0) =
      1 - prob (iidPMF q n) T := by
    have h1 := hμ.sum_eq_one
    have h2 : prob (iidPMF q n) T = ∑ ω, if ω ∈ T then iidPMF q n ω else 0 := by
      rw [sum_ite_mem, univ_inter]
      rfl
    calc ∑ ω, iidPMF q n ω * (if ω ∉ T then (1 : ℝ) else 0)
        = ∑ ω, (iidPMF q n ω - if ω ∈ T then iidPMF q n ω else 0) :=
          sum_congr rfl fun ω _ => by split_ifs <;> simp
      _ = _ := by rw [sum_sub_distrib, h1, h2]
  have havg : ∑ B, manyBinLaw M n α B * (code B).errProb q ≤
      (1 - prob (iidPMF q n) T) + K := by
    have e1 : ∀ B, manyBinLaw M n α B * (code B).errProb q = ∑ ω, iidPMF q n ω *
        (manyBinLaw M n α B * (if manyDec T B d (manyBin B ω) ≠ ω then (1 : ℝ) else 0)) :=
      fun B => by
        simp only [code, ManyCode.errProb, InfoTheory.errProb, mul_sum]
        refine sum_congr rfl fun ω _ => ?_
        have e2 : ManyCode.index ⟨fun j x => B j (Fintype.equivFin (Fin n → α j) x),
            manyDec T B d⟩ ω = manyBin B ω := rfl
        simp only [e2, id]
        split_ifs <;> ring
    simp only [e1]
    rw [sum_comm]
    calc ∑ ω, ∑ B, iidPMF q n ω * (manyBinLaw M n α B *
        (if manyDec T B d (manyBin B ω) ≠ ω then (1 : ℝ) else 0))
        = ∑ ω, iidPMF q n ω * ∑ B, manyBinLaw M n α B *
          (if manyDec T B d (manyBin B ω) ≠ ω then (1 : ℝ) else 0) :=
          sum_congr rfl fun ω _ => (mul_sum _ _ _).symm
      _ ≤ ∑ ω, iidPMF q n ω * ((if ω ∉ T then 1 else 0) + K) :=
          sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hω ω) (hμ.nonneg ω)
      _ = _ := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul, hsumT]
  obtain ⟨B, hB⟩ := exists_le_of_sum_mul_le hlaw havg
  exact ⟨code B, hB⟩

end Binning

/-! ### Theorem 3 -/

section Theorem

variable {q : (∀ j, α j) → ℝ}

/-- **Theorem 3 of Lecture 11, achievability.** A rate tuple with
`∑_{j ∈ S} Rⱼ > H(X(S) | X(Sᶜ))` for all nonempty `S` is achievable. -/
theorem isAchievableManyBits_of_lt (hq : IsPMF q) {R : ι → ℝ}
    (h : ∀ S : Finset ι, S.Nonempty → swCondH q S / log 2 < ∑ j ∈ S, R j) :
    IsAchievableManyBits q R := by
  classical
  have hl := log_pos one_lt_two
  have hH0 : ∀ S, 0 ≤ swCondH q S := fun S => condEntropy_nonneg hq _ _
  have hR : ∀ j, 0 ≤ R j := fun j => by
    have := h {j} (singleton_nonempty j)
    rw [sum_singleton] at this
    exact (div_nonneg (hH0 _) hl.le).trans this.le
  set N := univ.filter fun S : Finset ι => S.Nonempty with hN
  set G : Finset ι → ℝ := fun S => (∑ j ∈ S, R j) * log 2 - swCondH q S with hG
  have hGpos : ∀ S ∈ N, 0 < G S := fun S hS => by
    have := (div_lt_iff₀ hl).1 (h S (Finset.mem_filter.1 hS).2)
    simp only [hG]
    linarith
  obtain ⟨g, hg, hgG⟩ : ∃ g : ℝ, 0 < g ∧ ∀ S ∈ N, g ≤ G S := by
    rcases N.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun S hS => by simp [he] at hS⟩
    · obtain ⟨S₀, hS₀, hmin⟩ := N.exists_min_image G hne
      exact ⟨G S₀, hGpos S₀ hS₀, hmin⟩
  set B := ∑ S : Finset ι, swCondH q S + 1 with hB
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ S : Finset ι, swCondH q S := sum_nonneg fun S _ => hH0 S
    linarith
  have hHB : ∀ S, swCondH q S ≤ B := fun S => by
    have := single_le_sum (f := fun S => swCondH q S) (fun S _ => hH0 S) (mem_univ S)
    linarith
  set ε := min 1 (g / (2 * B)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hεH : ∀ S, ε * swCondH q S ≤ g / 2 := fun S => by
    have h1 : ε ≤ g / (2 * B) := min_le_right _ _
    calc ε * swCondH q S ≤ g / (2 * B) * B :=
          mul_le_mul h1 (hHB S) (hH0 S) (by positivity)
      _ = g / 2 := by
          field_simp
  set c₀ := exp ((Fintype.card ι : ℝ) * log 2) with hc₀
  set P : ℕ → ℝ := fun n => (1 - prob (iidPMF q n) (robustTypicalSet q n ε)) +
    (N.card : ℝ) * (c₀ * exp (-(n * (g / 2)))) with hP
  have hPlim : Tendsto P atTop (𝓝 0) := by
    have t₁ : Tendsto (fun n => 1 - prob (iidPMF q n) (robustTypicalSet q n ε)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet hq hε0).const_sub 1
    have t₂ := ((tendsto_exp_neg_mul_nat (half_pos hg)).const_mul c₀).const_mul (N.card : ℝ)
    simpa [hP] using t₁.add t₂
  have hcode : ∀ n : ℕ, ∃ c : ManyCode (fun j => 2 ^ ⌊n * R j⌋₊) n α, c.errProb q ≤ P n := by
    intro n
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨c, hc⟩ := exists_many_code_le (M := fun j => 2 ^ ⌊n * R j⌋₊) (n := n) (α := α) hq
      (fun j => by positivity) ε
    refine ⟨c, hc.trans (add_le_add le_rfl ?_)⟩
    calc ∑ S ∈ N, exp (n * (swCondH q S + ε * swCondH q S)) *
          ∏ j ∈ S, (1 / (((2 ^ ⌊n * R j⌋₊ : ℕ) : ℝ)))
        ≤ ∑ _S ∈ N, c₀ * exp (-(n * (g / 2))) := by
          refine sum_le_sum fun S hS => ?_
          have hp : ∏ j ∈ S, (1 / (((2 ^ ⌊n * R j⌋₊ : ℕ) : ℝ))) ≤
              ∏ j ∈ S, exp (-(n * (R j * log 2) - log 2)) := by
            refine prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
            rw [exp_neg, one_div]
            exact inv_anti₀ (exp_pos _) (exp_le_two_pow_floor n (R j))
          have hc2 : ((S.card : ℝ)) * log 2 ≤ (Fintype.card ι : ℝ) * log 2 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ S) hl.le
          refine (mul_le_mul_of_nonneg_left hp (exp_pos _).le).trans ?_
          rw [← exp_sum, ← exp_add, hc₀, ← exp_add]
          refine exp_le_exp.2 ?_
          have hsum : ∑ j ∈ S, -(n * (R j * log 2) - log 2) =
              -(n * ((∑ j ∈ S, R j) * log 2)) + (S.card : ℝ) * log 2 := by
            rw [sum_congr rfl fun j _ => (show -(n * (R j * log 2) - log 2) =
              log 2 - n * (R j * log 2) by ring), sum_sub_distrib, sum_const, nsmul_eq_mul,
              ← mul_sum, ← sum_mul]
            ring
          rw [hsum]
          have h1 := hgG S hS
          have h2 := hεH S
          simp only [hG] at h1
          have h3 : (n : ℝ) * (g / 2 + g / 2) ≤ n * ((∑ j ∈ S, R j) * log 2 - swCondH q S) :=
            mul_le_mul_of_nonneg_left (by linarith) hn0
          have h4 := mul_le_mul_of_nonneg_left h2 hn0
          nlinarith
      _ = _ := by
          rw [sum_const, nsmul_eq_mul]
  choose c hc using hcode
  exact ⟨hR, c, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hPlim
    (fun n => errProb_nonneg (iidPMF_isPMF hq n) _ _ _) hc⟩

/-- **Theorem 3 of Lecture 11 of [elgamal2010], page 11-32.** The optimal rate region of a `k`-DMS
is
the set of rate tuples with `∑_{j ∈ S} Rⱼ ≥ H(X(S) | X(Sᶜ))` for all `S ⊆ [1 : k]`, in bits. -/
theorem manyOptimalRegionBits_eq (hq : IsPMF q) : manyOptimalRegionBits q = manyRegionBits q := by
  refine subset_antisymm (closure_minimal (fun R hR => ?_) (isClosed_manyRegionBits q)) ?_
  · exact IsAchievableManyBits.mem_manyRegionBits hq hR
  · intro R hR
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun (n : ℕ) (j : ι) => R j + 1 / ((n : ℝ) + 1)) atTop (𝓝 R) := by
      refine tendsto_pi_nhds.2 fun j => ?_
      simpa using (tendsto_const_nhds (x := R j)).add ht
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    refine isAchievableManyBits_of_lt hq fun S hS => ?_
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have := mul_pos hc hp
    linarith [hR S]

end Theorem

end InfoTheory
