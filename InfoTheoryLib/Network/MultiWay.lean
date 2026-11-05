/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.SlepianWolfMany
public import InfoTheoryLib.Network.Transcript

/-!
# Multi-way lossless source coding: communication for omniscience

Theorem 3 of Lecture 21 of El Gamal and Kim. Each node `j` observes the source `Xⱼ`. The nodes
broadcast indices in rounds, and each index is a function of the source of its sender and of the
previous indices. All the nodes of a set `A` must recover all the sources. Interaction does not
help: the optimal region is given by the cutset bound, and it is achieved by binning, with one round
for each node.

## Main definitions

* `MWCode spk M n α`: a code, with the speaker `spk l` and `M l` indices in the round `l`.
* `IsAchievableMW`, `mwOptimalRegion`, `mwRegion`: the rate region.

## Main statements

* `MWCode.mul_swCondH_le`: the cutset bound for one code.
* `exists_mw_code_le`: the random binning bound.
* `mwOptimalRegion_eq`: **Theorem 3 of Lecture 21**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ j, Fintype (α j)]

/-- **Lecture 21 of [elgamal2010], page 21-15.** A code for communication for omniscience. In the
round `l` the node `spk l` broadcasts one of `M l` indices, a function of its source and of the
previous indices. The notes take the nodes in a round robin. Any other order is the same, with
trivial indices, so we let the order of the speakers be arbitrary. -/
structure MWCode {r : ℕ} (spk : Fin r → ι) (M : Fin r → ℕ) (n : ℕ) (α : ι → Type*) where
  /-- The encoder of the round `l`. -/
  enc : ∀ l, (Fin n → α (spk l)) → (∀ l', Fin (M l')) → Fin (M l)
  /-- The decoder of the node `k`, from its source and the indices. -/
  dec : ∀ k, (Fin n → α k) → (∀ l', Fin (M l')) → Fin n → ∀ j, α j

namespace MWCode

variable {r : ℕ} {spk : Fin r → ι} {M : Fin r → ℕ} [∀ l, NeZero (M l)] {n : ℕ}

instance : ∀ l, Nonempty (Fin (M l)) := fun _ => ⟨0⟩

/-- The transcript of the code, for the sequences of sources `ω`. -/
def trans (c : MWCode spk M n α) (ω : Fin n → ∀ j, α j) : ∀ l, Fin (M l) :=
  run fun l h => c.enc l (fun i => ω i (spk l)) h

/-- The estimate of all the sources at the node `k`. -/
def out (c : MWCode spk M n α) (ω : Fin n → ∀ j, α j) (k : ι) : Fin n → ∀ j, α j :=
  c.dec k (fun i => ω i k) (c.trans ω)

open Classical in
/-- The probability of error `P{X̂ⁿ_k ≠ Xⁿ for some k ∈ A}`. -/
def errProb (c : MWCode spk M n α) (p : (∀ j, α j) → ℝ) (A : Finset ι) : ℝ :=
  ∑ ω, iidPMF p n ω * if ∃ k ∈ A, c.out ω k ≠ ω then 1 else 0

end MWCode

/-- **Lecture 21 of [elgamal2010], page 21-16.** A rate tuple, in bits, is achievable if for every
`ε` and all large `n` there is a code with error at most `ε`, in any number of rounds, in which
the node `j` sends at most `2 ^ {n Rⱼ}` tuples of indices. -/
def IsAchievableMW (p : (∀ j, α j) → ℝ) (A : Finset ι) (R : ι → ℝ) : Prop :=
  (∀ j, 0 ≤ R j) ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (r : ℕ) (spk : Fin r → ι) (M : Fin r → ℕ)
    (_ : ∀ l, NeZero (M l)) (c : MWCode spk M n α),
    (∀ j, ∏ l with spk l = j, M l ≤ 2 ^ ⌊n * R j⌋₊) ∧ c.errProb p A ≤ ε

/-- **Lecture 21 of [elgamal2010], page 21-16.** The optimal rate region `R(A)`. -/
def mwOptimalRegion (p : (∀ j, α j) → ℝ) (A : Finset ι) : Set (ι → ℝ) :=
  closure {R | IsAchievableMW p A R}

/-- **Theorem 3 of Lecture 21 of [elgamal2010], page 21-16, the region.** The nonnegative rate
tuples with `∑_{j ∈ S} Rⱼ ≥ H(X(S) | X(Sᶜ))` for all `S` and all `k ∈ A` with `k ∉ S`, in bits. -/
def mwRegion (p : (∀ j, α j) → ℝ) (A : Finset ι) : Set (ι → ℝ) :=
  {R | (∀ j, 0 ≤ R j) ∧ ∀ k ∈ A, ∀ S : Finset ι, k ∉ S → swCondH p S / log 2 ≤ ∑ j ∈ S, R j}

lemma isClosed_mwRegion (p : (∀ j, α j) → ℝ) (A : Finset ι) : IsClosed (mwRegion p A) := by
  have e : mwRegion p A = (⋂ j, {R : ι → ℝ | 0 ≤ R j}) ∩ ⋂ k ∈ A, ⋂ S : Finset ι, ⋂ _ : k ∉ S,
      {R : ι → ℝ | swCondH p S / log 2 ≤ ∑ j ∈ S, R j} := by
    ext R
    simp [mwRegion]
  rw [e]
  refine (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter ?_
  exact isClosed_biInter fun k _ => isClosed_iInter fun S => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_finsetSum _ fun j _ => continuous_apply j)

/-- **Page 21-17 of [elgamal2010].** `R(A) = ⋂_{k ∈ A} R({k})`, for nonempty `A`. -/
theorem mwRegion_eq_iInter (p : (∀ j, α j) → ℝ) {A : Finset ι} (hA : A.Nonempty) :
    mwRegion p A = ⋂ k ∈ A, mwRegion p {k} := by
  ext R
  simp only [mwRegion, Set.mem_iInter, Set.mem_ofPred_eq, mem_singleton, forall_eq]
  constructor
  · exact fun h k hk => ⟨h.1, h.2 k hk⟩
  · intro h
    obtain ⟨k₀, hk₀⟩ := hA
    exact ⟨(h k₀ hk₀).1, fun k hk => (h k hk).2⟩

/-! ### The converse -/

section Converse

variable {r : ℕ} {spk : Fin r → ι} {M : Fin r → ℕ} [∀ l, NeZero (M l)] {n : ℕ}
  {p : (∀ j, α j) → ℝ}

open Classical in
/-- **Page 21-19 of [elgamal2010]: the cutset bound for one code.** Let `k ∈ A` and `k ∉ S`. Then
`n H(X(S) | X(Sᶜ)) ≤ ∑_{l : spk l ∈ S} log M_l + log 2 + Pₑ n log |𝒳|`. -/
theorem MWCode.mul_swCondH_le (c : MWCode spk M n α) (hp : IsPMF p) {A : Finset ι} {k : ι}
    (hkA : k ∈ A) {S : Finset ι} (hk : k ∉ S) :
    n * swCondH p S ≤ ∑ l with spk l ∈ S, log (M l) + log 2 +
      c.errProb p A * (n * log (Fintype.card (∀ j, α j))) := by
  have hμ := iidPMF_isPMF hp n
  set T := {l // spk l ∈ S} with hT
  set Y : (Fin n → ∀ j, α j) → Fin n → ∀ j : {j // j ∉ S}, α j := fun ω i => swRest S (ω i)
  set B : (Fin n → ∀ j, α j) → Fin n → ∀ j : S, α j := fun ω i => swPart S (ω i)
  set Ms : (Fin n → ∀ j, α j) → ∀ l : T, Fin (M l) := fun ω l => c.trans ω l
  rw [← condEntropy_iid_swPart hp n S]
  have hc1 := chain_rule_cond hμ B Ms Y
  have hc2 := chain_rule_cond hμ Ms B Y
  have hswap : H[pair B Ms | Y ; iidPMF p n] = H[pair Ms B | Y ; iidPMF p n] :=
    condEntropy_congr_left hμ Y Prod.swap Prod.swap_injective fun _ => rfl
  have h0 := condEntropy_nonneg hμ Ms (pair B Y)
  have hMs : H[Ms | Y ; iidPMF p n] ≤ ∑ l with spk l ∈ S, log (M l) := by
    refine (condEntropy_le_entropy hμ Ms Y).trans
      ((entropyRV_le_log_card hμ Ms).trans (le_of_eq ?_))
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    push_cast
    rw [log_prod fun l _ => by exact_mod_cast (NeZero.ne (M l))]
    exact (sum_subtype (univ.filter fun l => spk l ∈ S) (by simp) fun l => log (M l)).symm
  -- the transcript from `Ms` and `Y`
  let g : ((∀ l : T, Fin (M l)) × (Fin n → ∀ j : {j // j ∉ S}, α j)) → ∀ l, (∀ l', Fin (M l')) →
      Fin (M l) := fun w l h =>
    if hl : spk l ∈ S then w.1 ⟨l, hl⟩ else c.enc l (fun i => w.2 i ⟨spk l, hl⟩) h
  let dec' : ((∀ l : T, Fin (M l)) × (Fin n → ∀ j : {j // j ∉ S}, α j)) → Fin n → ∀ j, α j :=
    fun w => c.dec k (fun i => w.2 i ⟨k, hk⟩) (run (g w))
  have hrun : ∀ ω, run (g (Ms ω, Y ω)) = c.trans ω := fun ω => by
    refine (run_congr fun l => ?_).symm
    by_cases hl : spk l ∈ S
    · have := run_apply (fun l h => c.enc l (fun i => ω i (spk l)) h) l
      simp only [g, hl, ↓reduceDIte, Ms]
      exact this.symm
    · simp only [g, hl, ↓reduceDIte, Y, swRest]
  have hdec : ∀ ω, dec' (Ms ω, Y ω) = c.out ω k := fun ω => by
    simp only [dec', hrun]
    rfl
  have hfano := fano_weak hμ (id : (Fin n → ∀ j, α j) → _) (pair Ms Y) dec'
  have hcard : log (Fintype.card (Fin n → ∀ j, α j)) = n * log (Fintype.card (∀ j, α j)) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [log_pow]
  rw [hcard] at hfano
  have herr : InfoTheory.errProb (iidPMF p n) id (pair Ms Y) dec' ≤ c.errProb p A := by
    simp only [InfoTheory.errProb, MWCode.errProb]
    refine sum_le_sum fun ω _ => ?_
    have h₀ := iidPMF_nonneg hp.nonneg ω
    by_cases he : c.out ω k = ω
    · have e : dec' (pair Ms Y ω) = id ω := hdec ω |>.trans he
      simp only [e, ne_eq, not_true_eq_false, ite_false]
      split_ifs <;> simp [h₀]
    · have e : ∃ k ∈ A, c.out ω k ≠ ω := ⟨k, hkA, he⟩
      simp only [e, ite_true, mul_one]
      split_ifs <;> simp [h₀]
  have hle := condEntropy_comp_le' hμ (id : (Fin n → ∀ j, α j) → _) (pair Ms Y)
    (fun ω i => swPart S (ω i))
  have hB : (fun (ω : Fin n → ∀ j, α j) i => swPart S (ω i)) ∘ id = B := rfl
  rw [hB] at hle
  have hL : 0 ≤ (n : ℝ) * log (Fintype.card (∀ j, α j)) :=
    mul_nonneg (Nat.cast_nonneg n) (log_natCast_nonneg _)
  have := mul_le_mul_of_nonneg_right herr hL
  linarith

/-- **Page 21-19 of [elgamal2010]: the converse of Theorem 3.** -/
theorem IsAchievableMW.mem_mwRegion (hp : IsPMF p) {A : Finset ι} {R : ι → ℝ}
    (h : IsAchievableMW p A R) : R ∈ mwRegion p A := by
  classical
  refine ⟨h.1, fun k hk S hkS => ?_⟩
  have hl := log_pos one_lt_two
  refine (div_le_iff₀ hl).2 ?_
  set L := log (Fintype.card (∀ j, α j)) with hL
  have hL0 : 0 ≤ L := log_natCast_nonneg _
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (2 * (L + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨n, hn, hn1⟩ := ((h.2 ε hε0).and (eventually_gt_atTop ⌈2 * log 2 / δ⌉₊)).exists
  obtain ⟨r, spk, M, hM, c, hsize, herr⟩ := hn
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h₁ := c.mul_swCondH_le hp hk hkS
  have hsum : ∑ l with spk l ∈ S, log (M l) ≤ n * ((∑ j ∈ S, R j) * log 2) := by
    have e₁ : ∑ l with spk l ∈ S, log (M l) = ∑ j ∈ S, ∑ l with spk l = j, log (M l) := by
      rw [sum_filter, ← sum_filter (fun l => spk l ∈ S)]
      exact (sum_fiberwise_of_maps_to (t := S) (g := spk) (f := fun l => log (M l))
        (fun l hl => (mem_filter.1 hl).2)).symm.trans
        (sum_congr rfl fun j hj => sum_congr (by
          ext l
          simp only [mem_filter, mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨h ▸ hj, h⟩) fun _ _ => rfl)
    rw [e₁, sum_mul, mul_sum]
    refine sum_le_sum fun j _ => ?_
    have hpos : ∀ l, (0 : ℝ) < M l := fun l => by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne _)
    rw [← log_prod fun l _ => (hpos l).ne']
    refine le_trans (log_le_log (prod_pos fun l _ => hpos l) ?_) (log_two_pow_floor_le n (h.1 j))
    exact_mod_cast hsize j
  have h₂ : c.errProb p A * (n * L) ≤ ε * (n * L) :=
    mul_le_mul_of_nonneg_right herr (by positivity)
  have hn2 : log 2 / n ≤ δ / 2 := by
    have : 2 * log 2 / δ < n := (Nat.le_ceil _).trans_lt (by exact_mod_cast hn1)
    rw [div_lt_iff₀ hδ] at this
    rw [div_le_iff₀ hn0]
    linarith
  have h₃ : ε * L ≤ δ / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have key : (n : ℝ) * swCondH p S ≤ n * ((∑ j ∈ S, R j) * log 2 + δ) := by
    have h₄ : (n : ℝ) * (ε * L) ≤ n * (δ / 2) := mul_le_mul_of_nonneg_left h₃ hn0.le
    have h₅ : log 2 ≤ n * (δ / 2) := by
      rw [div_le_iff₀ hn0] at hn2
      linarith
    nlinarith
  exact le_of_mul_le_mul_left key hn0

end Converse

/-! ### Random binning -/

section Binning

variable {p : (∀ j, α j) → ℝ} {M : ι → ℕ} {n : ℕ} {r : ℕ} {spk : Fin r → ι}

open Classical in
/-- The decoder at the node `k`: the unique typical sequence with the source of `k` that falls in
the bins of the indices. -/
def mwDec (T : Finset (Fin n → ∀ j, α j)) (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (d : Fin n → ∀ j, α j) (spk : Fin r → ι) (k : ι) (x : Fin n → α k)
    (w : ∀ l, Fin (M (spk l))) : Fin n → ∀ j, α j :=
  if h : ∃ ω, ω ∈ T ∧ (∀ i, ω i k = x i) ∧ (∀ l, manyBin B ω (spk l) = w l) ∧
      ∀ ω' ∈ T, (∀ i, ω' i k = x i) → (∀ l, manyBin B ω' (spk l) = w l) → ω' = ω
  then h.choose else d

open Classical in
/-- The sequences that the decoder at `k` could confuse with `ω`. -/
def mwRivals (T : Finset (Fin n → ∀ j, α j)) (k : ι) (ω : Fin n → ∀ j, α j) :
    Finset (Fin n → ∀ j, α j) :=
  (T.erase ω).filter fun ω' => ∀ i, ω' i k = ω i k

open Classical in
lemma mwDec_ne_le (T : Finset (Fin n → ∀ j, α j)) (B : ∀ j, Fin (seqN α n j) → Fin (M j))
    (d ω : Fin n → ∀ j, α j) (hspk : Function.Surjective spk) (k : ι) :
    (if mwDec T B d spk k (fun i => ω i k) (fun l => manyBin B ω (spk l)) ≠ ω then (1 : ℝ) else 0) ≤
      (if ω ∉ T then 1 else 0) +
        ∑ ω' ∈ mwRivals T k ω, if ∀ j, manyBin B ω' j = manyBin B ω j then 1 else 0 := by
  have hn0 : (0 : ℝ) ≤ ∑ ω' ∈ mwRivals T k ω,
      if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0 :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hx : ω ∈ T
  · by_cases hu : ∀ ω' ∈ mwRivals T k ω, ¬ ∀ j, manyBin B ω' j = manyBin B ω j
    · have huniq : ∀ ω' ∈ T, (∀ i, ω' i k = ω i k) →
          (∀ l, manyBin B ω' (spk l) = manyBin B ω (spk l)) → ω' = ω := fun ω' h₁ h₂ h₃ => by
        by_contra hne
        refine hu ω' (mem_filter.2 ⟨mem_erase.2 ⟨hne, h₁⟩, h₂⟩) fun j => ?_
        obtain ⟨l, rfl⟩ := hspk j
        exact h₃ l
      have hex : ∃ ω₁, ω₁ ∈ T ∧ (∀ i, ω₁ i k = ω i k) ∧
          (∀ l, manyBin B ω₁ (spk l) = manyBin B ω (spk l)) ∧
          ∀ ω' ∈ T, (∀ i, ω' i k = ω i k) →
            (∀ l, manyBin B ω' (spk l) = manyBin B ω (spk l)) → ω' = ω₁ :=
        ⟨ω, hx, fun _ => rfl, fun _ => rfl, huniq⟩
      have hd : mwDec T B d spk k (fun i => ω i k) (fun l => manyBin B ω (spk l)) = ω := by
        simp only [mwDec]
        rw [dite_eq_left hex]
        exact huniq _ hex.choose_spec.1 hex.choose_spec.2.1 hex.choose_spec.2.2.1
      simp only [hd, ne_eq, not_true_eq_false, ite_false, hx, zero_add]
      exact hn0
    · push Not at hu
      obtain ⟨ω', hω', hb⟩ := hu
      have h1 : (1 : ℝ) ≤ ∑ ω' ∈ mwRivals T k ω,
          if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0 := by
        have := single_le_sum (f := fun ω' => if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ)
          else 0) (fun _ _ => by split_ifs <;> norm_num) hω'
        simpa [hb] using this
      split_ifs <;> linarith
  · simp only [hx, not_false_eq_true, ite_true]
    split_ifs <;> linarith

/-- The bound on the collisions, for one receiver. -/
def mwCollision (p : (∀ j, α j) → ℝ) (M : ι → ℕ) (n : ℕ) (ε : ℝ) (k : ι) : ℝ :=
  ∑ S ∈ univ.filter fun S : Finset ι => S.Nonempty ∧ k ∉ S,
    exp (n * (swCondH p S + ε * swCondH p S)) * ∏ j ∈ S, (1 / (M j : ℝ))

open Classical in
lemma sum_mwRivals_le (hp : IsPMF p) (ε : ℝ) (k : ι) (ω : Fin n → ∀ j, α j) :
    ∑ ω' ∈ mwRivals (robustTypicalSet p n ε) k ω,
      ∏ j ∈ univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j, (1 / (M j : ℝ)) ≤
      mwCollision p M n ε k := by
  set T := robustTypicalSet p n ε
  have hmaps : ∀ ω' ∈ mwRivals T k ω, (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) ∈
      univ.filter fun S : Finset ι => S.Nonempty ∧ k ∉ S := fun ω' hω' => by
    have h₁ := mem_filter.1 hω'
    refine Finset.mem_filter.2 ⟨mem_univ _, ?_, ?_⟩
    · by_contra hne
      refine (mem_erase.1 h₁.1).1 ?_
      funext i
      funext j
      have hj : (fun i => ω' i j) = fun i => ω i j := by
        by_contra h
        exact hne ⟨j, Finset.mem_filter.2 ⟨mem_univ _, h⟩⟩
      exact congrFun hj i
    · intro hk
      exact (mem_filter.1 hk).2 (funext h₁.2)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_le_sum fun S _ => ?_
  have hprod0 : (0 : ℝ) ≤ ∏ j ∈ S, (1 / (M j : ℝ)) := prod_nonneg fun _ _ => by positivity
  calc ∑ ω' ∈ (mwRivals T k ω).filter (fun ω' =>
        (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S),
        ∏ j ∈ univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j, (1 / (M j : ℝ))
      = ∑ ω' ∈ (mwRivals T k ω).filter (fun ω' =>
          (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S),
          ∏ j ∈ S, (1 / (M j : ℝ)) :=
        sum_congr rfl fun ω' hω' => by rw [(Finset.mem_filter.1 hω').2]
    _ = (((mwRivals T k ω).filter (fun ω' =>
          (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S)).card : ℝ) *
          ∏ j ∈ S, (1 / (M j : ℝ)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((((T.erase ω).filter fun ω' =>
          (univ.filter fun j => (fun i => ω' i j) ≠ fun i => ω i j) = S).card : ℝ)) *
          ∏ j ∈ S, (1 / (M j : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ hprod0
        exact_mod_cast card_le_card fun ω' hω' => by
          have h₁ := mem_filter.1 hω'
          exact mem_filter.2 ⟨(mem_filter.1 h₁.1).1, h₁.2⟩
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_filter_diff_le hp ω S) hprod0

open Classical in
/-- **Pages 21-18 of [elgamal2010]: random binning.** There is a code, with one round for each node,
such that `Pₑ ≤ P{Xⁿ ∉ T} + ∑_{k ∈ A} ∑_{S ≠ ∅, k ∉ S} e^{n(H(X(S) | X(Sᶜ)) + δ)} ∏_{j ∈ S} 1/Mⱼ`.
-/
theorem exists_mw_code_le (hp : IsPMF p) [∀ j, NeZero (M j)] (A : Finset ι) (ε : ℝ) :
    ∃ c : MWCode (Fintype.equivFin ι).symm (fun l => M ((Fintype.equivFin ι).symm l)) n α,
      c.errProb p A ≤ (1 - prob (iidPMF p n) (robustTypicalSet p n ε)) +
        ∑ k ∈ A, mwCollision p M n ε k := by
  have hμ := iidPMF_isPMF hp n
  have hMpos : ∀ j, 0 < M j := fun j => Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨z₀⟩ : Nonempty (∀ j, α j) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hp)
  set d : Fin n → ∀ j, α j := fun _ => z₀
  set T := robustTypicalSet p n ε
  have hlaw := manyBinLaw_isPMF (M := M) (n := n) (α := α) hMpos
  set e := (Fintype.equivFin ι).symm with he
  set K := ∑ k ∈ A, mwCollision p M n ε k with hKd
  let code : (∀ j, Fin (seqN α n j) → Fin (M j)) → MWCode e (fun l => M (e l)) n α := fun B =>
    ⟨fun l x _ => B (e l) (Fintype.equivFin (Fin n → α (e l)) x), mwDec T B d e⟩
  have htrans : ∀ B ω, (code B).trans ω = fun l => manyBin B ω (e l) := fun B ω => by
    funext l
    exact run_apply _ l
  have hω : ∀ ω : Fin n → ∀ j, α j, ∑ B, manyBinLaw M n α B *
      (if ∃ k ∈ A, (code B).out ω k ≠ ω then (1 : ℝ) else 0) ≤
      (if ω ∉ T then 1 else 0) + K := fun ω => by
    have hpt : ∀ B : ∀ j, Fin (seqN α n j) → Fin (M j),
        (if ∃ k ∈ A, (code B).out ω k ≠ ω then (1 : ℝ) else 0) ≤ (if ω ∉ T then 1 else 0) +
          ∑ k ∈ A, ∑ ω' ∈ mwRivals T k ω,
            if ∀ j, manyBin B ω' j = manyBin B ω j then 1 else 0 := fun B => by
      have h0 : (0 : ℝ) ≤ (if ω ∉ T then 1 else 0) := by split_ifs <;> norm_num
      have hsum0 : ∀ k, (0 : ℝ) ≤ ∑ ω' ∈ mwRivals T k ω,
          if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0 := fun k =>
        sum_nonneg fun _ _ => by split_ifs <;> norm_num
      by_cases hex : ∃ k ∈ A, (code B).out ω k ≠ ω
      · obtain ⟨k, hk, hne⟩ := hex
        have h₁ := mwDec_ne_le (spk := e) T B d ω e.surjective k
        have h₂ : mwDec T B d e k (fun i => ω i k) (fun l => manyBin B ω (e l)) ≠ ω := by
          have : (code B).out ω k =
              mwDec T B d e k (fun i => ω i k) (fun l => manyBin B ω (e l)) := by
            simp only [MWCode.out, htrans]
            rfl
          rwa [this] at hne
        simp only [h₂, ne_eq, not_false_eq_true, ite_true] at h₁
        have h₃ := single_le_sum (f := fun k => ∑ ω' ∈ mwRivals T k ω,
          if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0) (fun k _ => hsum0 k) hk
        rw [ite_eq_left ⟨k, hk, hne⟩]
        linarith
      · rw [ite_eq_right hex]
        exact add_nonneg h0 (sum_nonneg fun k _ => hsum0 k)
    calc ∑ B, manyBinLaw M n α B * (if ∃ k ∈ A, (code B).out ω k ≠ ω then (1 : ℝ) else 0)
        ≤ ∑ B, manyBinLaw M n α B * ((if ω ∉ T then 1 else 0) + ∑ k ∈ A, ∑ ω' ∈ mwRivals T k ω,
            if ∀ j, manyBin B ω' j = manyBin B ω j then 1 else 0) :=
          sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (hpt B) (hlaw.nonneg B)
      _ = (if ω ∉ T then 1 else 0) + ∑ k ∈ A, ∑ ω' ∈ mwRivals T k ω, ∑ B, manyBinLaw M n α B *
            (if ∀ j, manyBin B ω' j = manyBin B ω j then (1 : ℝ) else 0) := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hlaw.sum_eq_one, one_mul]
          congr 1
          simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun k _ => ?_
          exact sum_comm
      _ ≤ _ := by
          refine add_le_add le_rfl (sum_le_sum fun k _ => ?_)
          simp only [sum_manyBinLaw_collision hMpos]
          exact sum_mwRivals_le hp ε k ω
  have hsumT : ∑ ω, iidPMF p n ω * (if ω ∉ T then (1 : ℝ) else 0) =
      1 - prob (iidPMF p n) T := by
    have h1 := hμ.sum_eq_one
    have h2 : prob (iidPMF p n) T = ∑ ω, if ω ∈ T then iidPMF p n ω else 0 := by
      rw [sum_ite_mem, univ_inter]
      rfl
    calc ∑ ω, iidPMF p n ω * (if ω ∉ T then (1 : ℝ) else 0)
        = ∑ ω, (iidPMF p n ω - if ω ∈ T then iidPMF p n ω else 0) :=
          sum_congr rfl fun ω _ => by split_ifs <;> simp
      _ = _ := by rw [sum_sub_distrib, h1, h2]
  have havg : ∑ B, manyBinLaw M n α B * (code B).errProb p A ≤
      (1 - prob (iidPMF p n) T) + K := by
    simp only [MWCode.errProb, mul_sum]
    rw [sum_comm]
    calc ∑ ω, ∑ B, manyBinLaw M n α B * (iidPMF p n ω *
          (if ∃ k ∈ A, (code B).out ω k ≠ ω then (1 : ℝ) else 0))
        = ∑ ω, iidPMF p n ω * ∑ B, manyBinLaw M n α B *
          (if ∃ k ∈ A, (code B).out ω k ≠ ω then (1 : ℝ) else 0) :=
          sum_congr rfl fun ω _ => by
            rw [mul_sum]
            exact sum_congr rfl fun B _ => by ring
      _ ≤ ∑ ω, iidPMF p n ω * ((if ω ∉ T then 1 else 0) + K) :=
          sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hω ω) (hμ.nonneg ω)
      _ = _ := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hμ.sum_eq_one, one_mul, hsumT]
  obtain ⟨B, hB⟩ := exists_le_of_sum_mul_le hlaw havg
  exact ⟨code B, hB⟩

end Binning

/-! ### Theorem 3 -/

section Theorem

variable {p : (∀ j, α j) → ℝ}

/-- **Theorem 3 of Lecture 21, achievability.** -/
theorem isAchievableMW_of_lt (hp : IsPMF p) {A : Finset ι} {R : ι → ℝ} (hR : ∀ j, 0 ≤ R j)
    (h : ∀ k ∈ A, ∀ S : Finset ι, S.Nonempty → k ∉ S → swCondH p S / log 2 < ∑ j ∈ S, R j) :
    IsAchievableMW p A R := by
  classical
  have hl := log_pos one_lt_two
  have hH0 : ∀ S, 0 ≤ swCondH p S := fun S => condEntropy_nonneg hp _ _
  set N := univ.filter fun S : Finset ι => S.Nonempty ∧ ∃ k ∈ A, k ∉ S with hN
  set G : Finset ι → ℝ := fun S => (∑ j ∈ S, R j) * log 2 - swCondH p S with hG
  have hGpos : ∀ S ∈ N, 0 < G S := fun S hS => by
    obtain ⟨hne, k, hk, hkS⟩ := (mem_filter.1 hS).2
    have := (div_lt_iff₀ hl).1 (h k hk S hne hkS)
    simp only [hG]
    linarith
  obtain ⟨g, hg, hgG⟩ : ∃ g : ℝ, 0 < g ∧ ∀ S ∈ N, g ≤ G S := by
    rcases N.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun S hS => by simp [he] at hS⟩
    · obtain ⟨S₀, hS₀, hmin⟩ := N.exists_min_image G hne
      exact ⟨G S₀, hGpos S₀ hS₀, hmin⟩
  set B := ∑ S : Finset ι, swCondH p S + 1 with hB
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ S : Finset ι, swCondH p S := sum_nonneg fun S _ => hH0 S
    linarith
  have hHB : ∀ S, swCondH p S ≤ B := fun S => by
    have := single_le_sum (f := fun S => swCondH p S) (fun S _ => hH0 S) (mem_univ S)
    linarith
  set ε := min 1 (g / (2 * B)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hεH : ∀ S, ε * swCondH p S ≤ g / 2 := fun S => by
    have h1 : ε ≤ g / (2 * B) := min_le_right _ _
    calc ε * swCondH p S ≤ g / (2 * B) * B :=
          mul_le_mul h1 (hHB S) (hH0 S) (by positivity)
      _ = g / 2 := by
          field_simp
  set c₀ := exp ((Fintype.card ι : ℝ) * log 2) with hc₀
  set P : ℕ → ℝ := fun n => (1 - prob (iidPMF p n) (robustTypicalSet p n ε)) +
    (A.card : ℝ) * ((N.card : ℝ) * (c₀ * exp (-(n * (g / 2))))) with hP
  have hPlim : Tendsto P atTop (𝓝 0) := by
    have t₁ : Tendsto (fun n => 1 - prob (iidPMF p n) (robustTypicalSet p n ε)) atTop (𝓝 0) := by
      simpa using (tendsto_prob_robustTypicalSet hp hε0).const_sub 1
    have t₂ := (((tendsto_exp_neg_mul_nat (half_pos hg)).const_mul c₀).const_mul
      (N.card : ℝ)).const_mul (A.card : ℝ)
    simpa [hP] using t₁.add t₂
  refine ⟨hR, fun δ hδ => ?_⟩
  filter_upwards [(tendsto_order.1 hPlim).2 δ hδ] with n hn
  have hne : ∀ j, NeZero (2 ^ ⌊(n : ℝ) * R j⌋₊) := fun j => ⟨by positivity⟩
  set M : ι → ℕ := fun j => 2 ^ ⌊(n : ℝ) * R j⌋₊ with hM
  have hne' : ∀ j, NeZero (M j) := hne
  obtain ⟨c, hc⟩ := exists_mw_code_le (M := M) (n := n) (α := α) hp A ε
  refine ⟨_, _, _, fun l => hne' _, c, fun j => ?_, hc.trans ?_⟩
  · have e : (univ.filter fun l => (Fintype.equivFin ι).symm l = j) = {Fintype.equivFin ι j} := by
      ext l
      simp [Equiv.symm_apply_eq]
    rw [e, prod_singleton]
    simp [hM]
  · refine le_trans (add_le_add le_rfl ?_) hn.le
    have hone : ∀ k ∈ A, mwCollision p M n ε k ≤ (N.card : ℝ) * (c₀ * exp (-(n * (g / 2)))) := by
      intro k hk
      have hterm : ∀ S ∈ univ.filter fun S : Finset ι => S.Nonempty ∧ k ∉ S,
          exp (n * (swCondH p S + ε * swCondH p S)) * ∏ j ∈ S, (1 / (M j : ℝ)) ≤
            c₀ * exp (-(n * (g / 2))) := by
        intro S hS
        obtain ⟨hSne, hkS⟩ := (mem_filter.1 hS).2
        have hSN : S ∈ N := mem_filter.2 ⟨mem_univ _, hSne, k, hk, hkS⟩
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hpr : ∏ j ∈ S, (1 / (M j : ℝ)) ≤ ∏ j ∈ S, exp (-(n * (R j * log 2) - log 2)) := by
          refine prod_le_prod₀ (fun _ _ => by positivity) fun j _ => ?_
          rw [exp_neg, one_div]
          exact inv_anti₀ (exp_pos _) (exp_le_two_pow_floor n (R j))
        have hc2 : ((S.card : ℝ)) * log 2 ≤ (Fintype.card ι : ℝ) * log 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ S) hl.le
        refine (mul_le_mul_of_nonneg_left hpr (exp_pos _).le).trans ?_
        rw [← exp_sum, ← exp_add, hc₀, ← exp_add]
        refine exp_le_exp.2 ?_
        have hsum : ∑ j ∈ S, -(n * (R j * log 2) - log 2) =
            -(n * ((∑ j ∈ S, R j) * log 2)) + (S.card : ℝ) * log 2 := by
          rw [sum_congr rfl fun j _ => (show -(n * (R j * log 2) - log 2) =
            log 2 - n * (R j * log 2) by ring), sum_sub_distrib, sum_const, nsmul_eq_mul,
            ← mul_sum, ← sum_mul]
          ring
        rw [hsum]
        have h1 := hgG S hSN
        have h2 := hεH S
        simp only [hG] at h1
        have h3 : (n : ℝ) * (g / 2 + g / 2) ≤ n * ((∑ j ∈ S, R j) * log 2 - swCondH p S) :=
          mul_le_mul_of_nonneg_left (by linarith) hn0
        have h4 := mul_le_mul_of_nonneg_left h2 hn0
        nlinarith
      have hcard : ((univ.filter fun S : Finset ι => S.Nonempty ∧ k ∉ S).card : ℝ) ≤ N.card := by
        exact_mod_cast card_le_card fun S hS => by
          obtain ⟨hSne, hkS⟩ := (mem_filter.1 hS).2
          exact mem_filter.2 ⟨mem_univ _, hSne, k, hk, hkS⟩
      refine (sum_le_sum hterm).trans ?_
      rw [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    calc ∑ k ∈ A, mwCollision p M n ε k
        ≤ ∑ _k ∈ A, (N.card : ℝ) * (c₀ * exp (-(n * (g / 2)))) := sum_le_sum hone
      _ = _ := by
          rw [sum_const, nsmul_eq_mul]

/-- **Theorem 3 of Lecture 21 of [elgamal2010], page 21-16.** The optimal rate region of
  communication
for omniscience is the set of nonnegative rate tuples with `∑_{j ∈ S} Rⱼ ≥ H(X(S) | X(Sᶜ))` for all
`S` and `k ∈ A` with `k ∉ S`, in bits. In particular, interaction does not help. -/
theorem mwOptimalRegion_eq (hp : IsPMF p) (A : Finset ι) : mwOptimalRegion p A = mwRegion p A := by
  refine subset_antisymm (closure_minimal (fun R hR => ?_) (isClosed_mwRegion p A)) ?_
  · exact IsAchievableMW.mem_mwRegion hp hR
  · intro R hR
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun (n : ℕ) (j : ι) => R j + 1 / ((n : ℝ) + 1)) atTop (𝓝 R) := by
      refine tendsto_pi_nhds.2 fun j => ?_
      simpa using (tendsto_const_nhds (x := R j)).add ht
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hp' : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine isAchievableMW_of_lt hp (fun j => by linarith [hR.1 j]) fun k hk S hS hkS => ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have := mul_pos hc hp'
    linarith [hR.2 k hk S hkS]

/-- **Page 21-16 of [elgamal2010].** The minimum sum rate, in bits. -/
def rCFO (p : (∀ j, α j) → ℝ) (A : Finset ι) : ℝ :=
  sInf ((fun R : ι → ℝ => ∑ j, R j) '' mwRegion p A)

/-- With no coordinates, the conditional entropy is `0`. -/
lemma swCondH_empty (hp : IsPMF p) : swCondH p ∅ = 0 := by
  have hle := condEntropy_le_entropy hp (swPart (∅ : Finset ι)) (swRest ∅)
  have h₀ := condEntropy_nonneg hp (swPart (∅ : Finset ι)) (swRest ∅)
  have hcard : Fintype.card (∀ j : (∅ : Finset ι), α j) = 1 := by
    simp
  have h₁ := entropyRV_le_log_card hp (swPart (∅ : Finset ι))
  rw [hcard] at h₁
  simp only [Nat.cast_one, log_one] at h₁
  exact le_antisymm (hle.trans h₁) h₀

end Theorem

end InfoTheory
