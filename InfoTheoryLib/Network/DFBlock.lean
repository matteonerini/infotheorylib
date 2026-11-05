/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DFStrategy

/-!
# Decode–forward: the random code of one block

The code of a block has for each node `k` and each tag a sequence of strategies. The tag of a block
holds the messages `m_{j}, m_{j-1}, …`, where the entry `l` is the message of the index that node
`l` forwards. A strategy of node `k` depends only on the entries of the tag from `k` on.

## Main definitions

* `DFBlock`: the code of one block.
* `dfX d₀ C τ`: the sequence of the tuples of the inputs, for a tag `τ`.
* `dfTest`: the test of a decoder: the input of a node, the inputs of the nodes after it, and the
  output of the decoder are jointly typical.
* `dfE`: the exponent of the test.

## Main statements

* `sum_dfBlock_true`: the sequence of the tuples for a tag is i.i.d.
* `sum_dfBlock_test_le`: **the bound on the test for a wrong message**.

## Implementation notes

The notes draw the codeword of node `k` given the codewords of the nodes after `k`. We use random
strategies, so that all the entries of the code are independent.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Tag

variable {N Mm n : ℕ} {X : Fin N → Type*} [NeZero Mm]

/-- The tags of a block. -/
abbrev DFTag (N Mm : ℕ) := Fin N → Fin Mm

/-- The part of a tag from node `k` on. -/
def dfCanon (k : Fin N) (τ : DFTag N Mm) : DFTag N Mm := fun l => if (k : ℕ) ≤ l then τ l else 0

/-- The code of one block: a sequence of strategies for each node and each tag. -/
abbrev DFBlock (N Mm n : ℕ) (X : Fin N → Type*) :=
  ∀ k : Fin N, DFTag N Mm → Fin n → NetStrat X k

/-- The strategies of a block at time `i`, for a tag. -/
def dfStrats (C : DFBlock N Mm n X) (τ : DFTag N Mm) (i : Fin n) : ∀ k, NetStrat X k :=
  fun k => C k (dfCanon k τ) i

variable [∀ k, DecidableEq (X k)] (d₀ : ∀ l, X l)

/-- The tuples of the inputs for a tag. -/
def dfX (C : DFBlock N Mm n X) (τ : DFTag N Mm) (i : Fin n) : ∀ l, X l :=
  buildAt d₀ (dfStrats C τ i) 0

/-- The tuple from `j` on depends only on the tag from `j` on. -/
lemma fillGe_dfX_congr (C : DFBlock N Mm n X) {τ τ' : DFTag N Mm} {j : ℕ}
    (h : ∀ l : Fin N, j ≤ l → τ l = τ' l) (i : Fin n) :
    fillGe d₀ j (dfX d₀ C τ i) = fillGe d₀ j (dfX d₀ C τ' i) := by
  simp only [dfX]
  rw [← buildAt_eq_fillGe, ← buildAt_eq_fillGe]
  refine buildAt_congr d₀ _ j rfl fun k hk => ?_
  simp only [dfStrats]
  congr 1
  funext l
  simp only [dfCanon]
  split_ifs with hl
  · exact h l (hk.trans hl)
  · rfl

/-- The input of a node is its strategy, applied to the inputs of the nodes after it. -/
lemma dfX_apply (C : DFBlock N Mm n X) (τ : DFTag N Mm) (i : Fin n) (k : Fin N) :
    dfX d₀ C τ i k = C k (dfCanon k τ) i (fillGe d₀ (k + 1) (dfX d₀ C τ i)) :=
  buildAt_zero_apply d₀ _ k

/-- The input of a node depends only on the tag from that node on. -/
lemma dfX_congr (C : DFBlock N Mm n X) {τ τ' : DFTag N Mm} {k : Fin N}
    (h : ∀ l : Fin N, (k : ℕ) ≤ l → τ l = τ' l) (i : Fin n) :
    dfX d₀ C τ i k = dfX d₀ C τ' i k := by
  have := congrFun (fillGe_dfX_congr d₀ C h i) k
  simpa [fillGe] using this

end Tag

/-! ### The laws -/

section Laws

variable {N Mm n : ℕ} {X Y : Fin N → Type*} [NeZero Mm] [∀ k, Fintype (X k)]
  [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] (d₀ : ∀ l, X l) {p : (∀ l, X l) → ℝ}
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {κ : ∀ k, (∀ l, X l) → X k → ℝ}

/-- The law of the code of one block. -/
def dfBlockLaw (κ : ∀ k, (∀ l, X l) → X k → ℝ) (Mm n : ℕ) (C : DFBlock N Mm n X) : ℝ :=
  prodLaw (fun k => piLaw fun _ : DFTag N Mm => iidPMF (netStratLaw (κ k)) n) C

omit [NeZero Mm] [∀ k, Fintype (Y k)] in
lemma dfBlockLaw_isPMF (hκc : ∀ k, IsChannel (κ k)) : IsPMF (dfBlockLaw (X := X) κ Mm n) :=
  prodLaw_isPMF fun k => piLaw_isPMF fun _ => iidPMF_isPMF (netStratLaw_isPMF (hκc k)) n

/-- **One more entry of a table is independent of the other entries.** -/
theorem sum_prodLaw_eval_extra {A : Fin N → Type*} {R : Fin N → Type*} [∀ k, Fintype (A k)]
    [∀ k, Fintype (R k)] [∀ k, DecidableEq (A k)] {ρ : ∀ k, R k → ℝ} (hρ : ∀ k, IsPMF (ρ k))
    (a : ∀ k, A k) (k' : Fin N) {b : A k'} (hb : b ≠ a k') (G : (∀ k, R k) → R k' → ℝ) :
    ∑ C : ∀ k, A k → R k, prodLaw (fun k => piLaw fun _ : A k => ρ k) C *
        G (fun k => C k (a k)) (C k' b) =
      ∑ u : ∀ k, R k, prodLaw ρ u * ∑ w, ρ k' w * G u w := by
  classical
  have hsplit : ∀ C : ∀ k, A k → R k, prodLaw (fun k => piLaw fun _ : A k => ρ k) C *
      G (fun k => C k (a k)) (C k' b) = ∑ w, prodLaw (Function.update
        (fun k => piLaw fun _ : A k => ρ k) k' fun c => piLaw (fun _ : A k' => ρ k') c * ind (c b =
          w)) C *
        G (fun k => C k (a k)) w := by
    intro C
    rw [Finset.sum_eq_single (C k' b)]
    · congr 1
      simp only [prodLaw]
      refine prod_congr rfl fun k _ => ?_
      by_cases hk : k = k'
      · subst hk
        rw [Function.update_self, ind_of_pos rfl, mul_one]
      · rw [Function.update_of_ne hk]
    · intro w _ hw
      have : prodLaw (Function.update (fun k => piLaw fun _ : A k => ρ k) k'
          fun c => piLaw (fun _ : A k' => ρ k') c * ind (c b = w)) C = 0 := by
        refine prod_eq_zero (mem_univ k') ?_
        rw [Function.update_self, ind_of_neg (Ne.symm hw), mul_zero]
      rw [this, zero_mul]
    · simp
  simp_rw [hsplit]
  rw [sum_comm]
  have hw : ∀ w, ∑ C : ∀ k, A k → R k, prodLaw (Function.update
      (fun k => piLaw fun _ : A k => ρ k) k' fun c => piLaw (fun _ : A k' => ρ k') c * ind (c b =
        w)) C *
      G (fun k => C k (a k)) w = ∑ u : ∀ k, R k, prodLaw ρ u * (ρ k' w * G u w) := by
    intro w
    have h₁ := sum_prodLaw_comp (Function.update (fun k => piLaw fun _ : A k => ρ k) k'
      fun c => piLaw (fun _ : A k' => ρ k') c * ind (c b = w)) (fun k c => c (a k)) fun u => G u w
    rw [h₁]
    refine sum_congr rfl fun u _ => ?_
    have h₂ : prodLaw (fun k => dist (Function.update (fun k => piLaw fun _ : A k => ρ k) k'
        (fun c => piLaw (fun _ : A k' => ρ k') c * ind (c b = w)) k) fun c => c (a k)) u =
        prodLaw ρ u * ρ k' w := by
      simp only [prodLaw]
      rw [← mul_prod_erase univ _ (mem_univ k'), ← mul_prod_erase univ (fun k => ρ k (u k))
        (mem_univ k'), mul_right_comm]
      congr 1
      · rw [Function.update_self]
        have := sum_piLaw_mul_eval₂ (ν := fun _ : A k' => ρ k') (fun _ => hρ k') hb.symm
          fun v v' => ind (v = u k') * ind (v' = w)
        simp only [dist]
        have e : ∀ c : A k' → R k', (if c (a k') = u k' then
            piLaw (fun _ : A k' => ρ k') c * ind (c b = w) else 0) =
            piLaw (fun _ : A k' => ρ k') c * (ind (c (a k') = u k') * ind (c b = w)) := by
          intro c
          simp only [ind]
          split_ifs <;> simp
        simp_rw [e]
        rw [this, Finset.sum_eq_single (u k'), Finset.sum_eq_single w]
        · rw [ind_of_pos rfl, ind_of_pos rfl, mul_one, mul_one]
        · exact fun v _ hv => by rw [ind_of_neg hv, mul_zero, mul_zero]
        · simp
        · intro v _ hv
          refine sum_eq_zero fun v' _ => ?_
          rw [ind_of_neg hv, zero_mul, mul_zero]
        · simp
      · refine prod_congr rfl fun k hk => ?_
        have hne := ne_of_mem_erase hk
        simp only [Function.update_of_ne hne]
        have := sum_piLaw_mul_eval (ν := fun _ : A k => ρ k) (fun _ => hρ k) (a k)
          fun v => ind (v = u k)
        simp only [dist]
        have e : ∀ c : A k → R k, (if c (a k) = u k then piLaw (fun _ : A k => ρ k) c else 0) =
            piLaw (fun _ : A k => ρ k) c * ind (c (a k) = u k) := by
          intro c
          simp only [ind]
          split_ifs <;> simp
        simp_rw [e]
        rw [this, Finset.sum_eq_single (u k)]
        · rw [ind_of_pos rfl, mul_one]
        · exact fun v _ hv => by rw [ind_of_neg hv, mul_zero]
        · simp
    rw [h₂, mul_assoc]
  simp_rw [hw]
  rw [sum_comm]
  refine sum_congr rfl fun u _ => ?_
  rw [mul_sum]

/-- The law of one entry of a table. -/
lemma dist_piLaw_apply {A R : Type*} [Fintype A] [Fintype R] [DecidableEq A] {ρ : A → R → ℝ}
    (hρ : ∀ a, IsPMF (ρ a)) (a : A) : dist (piLaw ρ) (fun c => c a) = ρ a := by
  classical
  funext r
  have h := sum_piLaw_mul_eval hρ a fun v => ind (v = r)
  rw [Finset.sum_eq_single r (fun v _ hv => by rw [ind_of_neg hv, mul_zero]) (by simp),
    ind_of_pos rfl, mul_one] at h
  rw [← h]
  simp only [dist, ind]
  refine sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

/-- **The sequence of the tuples for a tag is i.i.d.** -/
theorem sum_dfBlock_true (hp : IsPMF p) (hκc : ∀ k, IsChannel (κ k))
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) (τ : DFTag N Mm)
    (G : (Fin n → ∀ l, X l) → ℝ) :
    ∑ C, dfBlockLaw κ Mm n C * G (dfX d₀ C τ) = ∑ x, iidPMF p n x * G x := by
  classical
  have hσ : ∀ k, IsPMF (netStratLaw (κ k)) := fun k => netStratLaw_isPMF (hκc k)
  -- the strategies of the tag
  have h₁ := sum_prodLaw_comp (fun k => piLaw fun _ : DFTag N Mm => iidPMF (netStratLaw (κ k)) n)
    (fun k (c : DFTag N Mm → Fin n → NetStrat X k) => c (dfCanon k τ))
    fun u => G fun i => buildAt d₀ (fun k => u k i) 0
  have h₂ : ∑ C, dfBlockLaw κ Mm n C * G (dfX d₀ C τ) = ∑ u : ∀ k, Fin n → NetStrat X k,
      prodLaw (fun k => iidPMF (netStratLaw (κ k)) n) u *
        G (fun i => buildAt d₀ (fun k => u k i) 0) := by
    refine h₁.trans (sum_congr rfl fun u _ => ?_)
    congr 2
    funext k
    exact dist_piLaw_apply (fun _ => iidPMF_isPMF (hσ k) n) _
  rw [h₂]
  -- the law of a tuple of strategies
  let ς : (∀ k, NetStrat X k) → ℝ := prodLaw fun k => netStratLaw (κ k)
  have hς : dist ς (fun s => buildAt d₀ s 0) = p := by
    funext x
    rw [← sum_strat_build d₀ hp hκc hκ x]
    simp only [dist, ς, ind]
    refine sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  have h₃ : ∑ u : ∀ k, Fin n → NetStrat X k, prodLaw (fun k => iidPMF (netStratLaw (κ k)) n) u *
      G (fun i => buildAt d₀ (fun k => u k i) 0) = ∑ w : Fin n → ∀ k, NetStrat X k,
        iidPMF ς n w * G fun i => buildAt d₀ (w i) 0 := by
    refine Fintype.sum_equiv (Equiv.piComm _) _ _ fun u => ?_
    congr 1
    simp only [prodLaw, iidPMF, ς]
    exact prod_comm
  have hc : dist (iidPMF ς n) (fun w i => buildAt d₀ (w i) 0) = iidPMF p n := by
    rw [← hς]
    exact dist_iidPMF_comp ς n fun s => buildAt d₀ s 0
  rw [h₃, ← sum_dist_mul (iidPMF ς n) (fun w i => buildAt d₀ (w i) 0) G, hc]

variable (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ)

/-- The law of what a decoder tests: `((X_{k+1}^N, Y_d), X_k)`. -/
def dfLT (k d : Fin N) : ((∀ l, X l) × Y d) × X k → ℝ :=
  dist L₀ fun ω => ((fillGe d₀ (k + 1) ω.1, ω.2 d), ω.1 k)

/-- **The test of a decoder**: the input of node `k`, the inputs of the nodes after `k`, and the
output of the decoder `d` are jointly typical. -/
def dfTest (k d : Fin N) (ε : ℝ) (x : Fin n → ∀ l, X l) (yd : Fin n → Y d) : Prop :=
  (fun i => ((fillGe d₀ (k + 1) (x i), yd i), x i k)) ∈ robustTypicalSet (dfLT d₀ L₀ k d) n ε

/-- **Page 19-16 of [elgamal2010].** The exponent of the test, `I(X_k; Y_d | X_{k+1}^N)`. -/
def dfE (k d : Fin N) : ℝ :=
  H[Prod.fst ; dfLT d₀ L₀ k d] + H[fun z : ((∀ l, X l) × Y d) × X k => (z.1.1, z.2) ; dfLT d₀ L₀ k
    d] -
    H[fun z : ((∀ l, X l) × Y d) × X k => z.1.1 ; dfLT d₀ L₀ k d] - entropy (dfLT d₀ L₀ k d)

/-- The constant in front of the typicality parameter. -/
def dfC (k d : Fin N) : ℝ :=
  entropy (dfLT d₀ L₀ k d) + H[Prod.fst ; dfLT d₀ L₀ k d] +
    H[fun z : ((∀ l, X l) × Y d) × X k => (z.1.1, z.2) ; dfLT d₀ L₀ k d] +
    H[fun z : ((∀ l, X l) × Y d) × X k => z.1.1 ; dfLT d₀ L₀ k d]

/-- **The bound on the test for a wrong message.** Let the tag `τ'` differ from the true tag `τ` at
node `k`, and agree with it after `k`. Then the sequence of node `k` for `τ'` is fresh. -/
theorem sum_dfBlock_test_le (hW : IsChannel W) (hp : IsPMF p) (hκc : ∀ k, IsChannel (κ k))
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) {τ τ' : DFTag N Mm}
    (k d : Fin N) (hne : τ' k ≠ τ k) (hag : ∀ l : Fin N, (k : ℕ) < l → τ' l = τ l) (ε : ℝ) :
    ∑ C, dfBlockLaw κ Mm n C * ∑ y, seqChan W n (dfX d₀ C τ) y *
      ind (dfTest d₀ (jointOf p W) k d ε (dfX d₀ C τ') (fun i => y i d)) ≤
    exp (-(n * (dfE d₀ (jointOf p W) k d - ε * dfC d₀ (jointOf p W) k d))) := by
  classical
  set L₁ := jointOf p W with hL₁
  have hL₁P : IsPMF L₁ := jointOf_isPMF hp hW
  set LT := dfLT d₀ L₁ k d with hLT
  have hLTP : IsPMF LT := hL₁P.dist _
  have hσ : ∀ k, IsPMF (netStratLaw (κ k)) := fun k => netStratLaw_isPMF (hκc k)
  have hρ : ∀ k, IsPMF (iidPMF (netStratLaw (κ k)) n) := fun k => iidPMF_isPMF (hσ k) n
  -- the law of the fresh sequence
  have hfresh : ∀ (u : Fin n → ∀ l, X l) (yd : Fin n → Y d),
      ∑ w : Fin n → NetStrat X k, iidPMF (netStratLaw (κ k)) n w *
        ind ((fun i => ((fillGe d₀ (k + 1) (u i), yd i), w i (fillGe d₀ (k + 1) (u i)))) ∈
          robustTypicalSet LT n ε) ≤
      exp (-(n * (dfE d₀ L₁ k d - ε * dfC d₀ L₁ k d))) := by
    intro u yd
    let r : Fin n → (∀ l, X l) × Y d := fun i => (fillGe d₀ (k + 1) (u i), yd i)
    have hg : ∀ (c : ∀ l, X l) (a : X k), dist LT (fun z : ((∀ l, X l) × Y d) × X k =>
        (z.1.1, z.2)) (c, a) = dist LT (fun z : ((∀ l, X l) × Y d) × X k => z.1.1) c * κ k c a := by
      intro c a
      have h₁ : dist LT (fun z : ((∀ l, X l) × Y d) × X k => (z.1.1, z.2)) = dfJoint p d₀ k := by
        rw [hLT, dfLT, ← dist_comp_eq]
        have e : ((fun z : ((∀ l, X l) × Y d) × X k => (z.1.1, z.2)) ∘
            fun ω : (∀ l, X l) × (∀ l, Y l) => ((fillGe d₀ (k + 1) ω.1, ω.2 d), ω.1 k)) =
            (fun x : ∀ l, X l => (fillGe d₀ (k + 1) x, x k)) ∘ Prod.fst := rfl
        rw [e, dist_comp_eq, hL₁, dist_jointOf_fst hW]
        rfl
      have h₂ : dist LT (fun z : ((∀ l, X l) × Y d) × X k => z.1.1) = marg (dfJoint p d₀ k) := by
        funext c'
        rw [marg_eq_dist, ← h₁, ← dist_comp_eq]
        rfl
      rw [h₁, h₂]
      exact hκ k c a
    have hb := sum_fresh_point hLTP (fun z : (∀ l, X l) × Y d => z.1) hg (hκc k) (n := n) (ε := ε)
      (fun a t => (fun i => (a i, t i)) ∈ robustTypicalSet LT n ε) (fun _ _ h => h) r
    have hpush := sum_prodLaw_comp (fun _ : Fin n => netStratLaw (κ k))
      (fun i (s : NetStrat X k) => s (r i).1) fun t : Fin n → X k =>
        ind ((fun i => (r i, t i)) ∈ robustTypicalSet LT n ε)
    have hd : ∀ (i : Fin n) (a : X k), dist (netStratLaw (κ k)) (fun s : NetStrat X k => s (r i).1)
      a =
        κ k (r i).1 a := fun i a =>
      congrFun (dist_piLaw_apply (ρ := fun c => κ k c) (hκc k) (r i).1) a
    refine le_trans (le_of_eq ?_) hb
    refine Eq.trans hpush (sum_congr rfl fun t _ => ?_)
    congr 1
    simp only [prodLaw, seqChan]
    exact prod_congr rfl fun i _ => hd i (t i)
  -- the code
  have hbne : dfCanon k τ' ≠ dfCanon k τ := fun h => hne (by
    have := congrFun h k
    simpa [dfCanon] using this)
  have hsum := sum_prodLaw_eval_extra hρ (fun k => dfCanon k τ) k hbne
    fun (u : ∀ k, Fin n → NetStrat X k) (w : Fin n → NetStrat X k) =>
      ∑ y, seqChan W n (fun i => buildAt d₀ (fun k => u k i) 0) y *
        ind ((fun i => ((fillGe d₀ (k + 1) (buildAt d₀ (fun k => u k i) 0), y i d),
          w i (fillGe d₀ (k + 1) (buildAt d₀ (fun k => u k i) 0)))) ∈ robustTypicalSet LT n ε)
  have hrw : ∀ C : DFBlock N Mm n X, ∑ y, seqChan W n (dfX d₀ C τ) y *
      ind (dfTest d₀ L₁ k d ε (dfX d₀ C τ') (fun i => y i d)) =
      ∑ y, seqChan W n (fun i => buildAt d₀ (fun k' => C k' (dfCanon k' τ) i) 0) y *
        ind ((fun i => ((fillGe d₀ (k + 1) (buildAt d₀ (fun k' => C k' (dfCanon k' τ) i) 0), y i d),
          C k (dfCanon k τ') i (fillGe d₀ (k + 1)
            (buildAt d₀ (fun k' => C k' (dfCanon k' τ) i) 0)))) ∈ robustTypicalSet LT n ε) := by
    intro C
    refine sum_congr rfl fun y _ => ?_
    congr 2
    have hfill : ∀ i, fillGe d₀ (k + 1) (dfX d₀ C τ' i) = fillGe d₀ (k + 1) (dfX d₀ C τ i) :=
      fun i => fillGe_dfX_congr d₀ C (fun l hl => hag l (by omega)) i
    simp only [dfTest]
    refine propext (iff_of_eq ?_)
    congr 1
    funext i
    rw [hfill i, dfX_apply d₀ C τ' i k, hfill i]
    rfl
  simp_rw [hrw]
  have hfin := hsum
  simp only [dfBlockLaw]
  refine hfin.le.trans ?_
  set E := exp (-(n * (dfE d₀ L₁ k d - ε * dfC d₀ L₁ k d))) with hE
  have hE0 : 0 ≤ E := (exp_pos _).le
  calc _ ≤ ∑ u : ∀ k, Fin n → NetStrat X k, prodLaw (fun k => iidPMF (netStratLaw (κ k)) n) u *
    E := by
        refine sum_le_sum fun u _ => mul_le_mul_of_nonneg_left ?_ (prodLaw_nonneg hρ u)
        simp_rw [mul_sum]
        rw [sum_comm]
        calc _ = ∑ y, seqChan W n (fun i => buildAt d₀ (fun k => u k i) 0) y *
              ∑ w : Fin n → NetStrat X k, iidPMF (netStratLaw (κ k)) n w *
                ind ((fun i => ((fillGe d₀ (k + 1) (buildAt d₀ (fun k => u k i) 0), y i d),
                  w i (fillGe d₀ (k + 1) (buildAt d₀ (fun k => u k i) 0)))) ∈
                    robustTypicalSet LT n ε) := by
              refine sum_congr rfl fun y _ => ?_
              rw [mul_sum]
              exact sum_congr rfl fun w _ => by ring
          _ ≤ ∑ y, seqChan W n (fun i => buildAt d₀ (fun k => u k i) 0) y * E :=
              sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
                (hfresh (fun i => buildAt d₀ (fun k => u k i) 0) fun i => y i d)
                ((seqChan_isChannel hW n _).nonneg _)
          _ = E := by rw [← sum_mul, (seqChan_isChannel hW n _).sum_eq_one, one_mul]
    _ = E := by rw [← sum_mul, (prodLaw_isPMF hρ).sum_eq_one, one_mul]

end Laws

end InfoTheory
