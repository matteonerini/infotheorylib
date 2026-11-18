/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DFGenie

/-!
# Decode–forward: the code of all the blocks

## Main definitions

* `dfMsg μ`: a sequence of messages as a function on the natural numbers.
* `dfCode`: the code of all the blocks. The source sends a sequence of messages, and each relay
  forwards the messages it has decoded.

## Main statements

* `dfCode_law`: the law of the code as a product over the blocks.
* `dfCode_not_wrong_of_good`: on the good event of the genie run, the actual run is the genie run
  and the destinations decode.
* `dfCode_avg_le`: **the average of the probability of error over the codes of the blocks**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Code

variable {N Mm n B' : ℕ} {X Y : Fin N → Type*} [NeZero Mm] [NeZero n] [∀ k, Fintype (X k)]
  [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] {M : Fin N → ℕ}

/-- A sequence of messages, with the message `0` after the last one. -/
def dfMsg (μ : Fin B' → Fin Mm) (j : ℕ) : Fin Mm := if h : j < B' then μ ⟨j, h⟩ else 0

omit [∀ k, Fintype (X k)] in
lemma dfMsg_zero (μ : Fin B' → Fin Mm) (j : ℕ) (h : B' ≤ j) : dfMsg μ j = 0 := by
  simp [dfMsg, not_lt.mpr h]

/-- The sequence of messages of the source, as a function of the message of node `k`. -/
def dfSrc (s₀ : Fin N) (e : Fin (M s₀) → Fin B' → Fin Mm) (k : Fin N) (mk : Fin (M k)) :
    ℕ → Fin Mm :=
  if h : k = s₀ then dfMsg (e (h ▸ mk)) else fun _ => 0

/-- **Pages 19-13 to 19-16 of [elgamal2010].** The code of all the blocks. The source `s₀` sends the
sequence of messages `e m`, and each node forwards what it has decoded. A decoder decodes the
messages one after the other. -/
def dfCode (d₀ : ∀ l, X l) (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ)
    (Cs : ℕ → DFBlock N Mm n X) (s₀ : Fin N) (e : Fin (M s₀) → Fin B' → Fin Mm) (dY : ∀ k, Y k)
    (hM : ∀ k, 0 < M k) (N' : ℕ) : DMNCode M N' X Y where
  enc k i mk y :=
    if k = s₀ then dfX d₀ (Cs (i / n)) (dfTagOf (dfSrc s₀ e k mk) (i / n))
      ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩ k
    else dfX d₀ (Cs (i / n)) (dfTagD d₀ L₀ ε Cs B' k (getBlock (dY k) y) (i / n))
      ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩ k
  dec k _ y :=
    have : Nonempty (Fin (M s₀)) := ⟨⟨0, hM s₀⟩⟩
    Function.update (fun j => ⟨0, hM j⟩) s₀ (Function.invFun e fun j : Fin B' =>
      dfEst d₀ L₀ ε Cs B' k (getBlock (dY k) y) j)

variable {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {t : ℕ}

/-- The inputs of a block of the actual run. -/
def dfRx (d₀ : ∀ l, X l) (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ) (Cs : ℕ → DFBlock N Mm n X)
    (s₀ : Fin N) (msg : ℕ → Fin Mm) (dY : ∀ k, Y k) (z : Fin t → ∀ k, Y k) (B : ℕ) (i : Fin n)
    (k : Fin N) : X k :=
  if k = s₀ then dfX d₀ (Cs B) (dfTagOf msg B) i k
  else dfX d₀ (Cs B) (dfTagD d₀ L₀ ε Cs B' k (getBlock (dY k) fun s => z s k) B) i k

omit [∀ k, DecidableEq (X k)] in
/-- **The law of the code of all the blocks** is a product over the blocks. -/
theorem dfCode_law (d₀ : ∀ l, X l) (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ)
    (Cs : ℕ → DFBlock N Mm n X) (s₀ : Fin N) (e : Fin (M s₀) → Fin B' → Fin Mm) (dY : ∀ k, Y k)
    (hM : ∀ k, 0 < M k) (m : ∀ k, Fin (M k)) (z : Fin (t * n) → ∀ k, Y k) :
    (dfCode d₀ L₀ ε Cs s₀ e dY hM (t * n)).law W (m, z) =
      uniformPMF (∀ k, Fin (M k)) m * ∏ B : Fin t, seqChan W n
        (dfRx (B' := B') d₀ L₀ ε Cs s₀ (dfMsg (e (m s₀))) dY z B) (nncBlocks z B) := by
  rw [DMNCode.law, fbLaw_eq_prod]
  congr 1
  rw [← Equiv.prod_comp finProdFinEquiv, Fintype.prod_prod_type]
  refine prod_congr rfl fun B _ => ?_
  simp only [seqChan]
  refine prod_congr rfl fun i _ => ?_
  obtain ⟨hdiv, hmod⟩ := finProd_div_mod' (t := t) (NeZero.pos n) B i
  have hin : (⟨((finProdFinEquiv (B, i) : Fin (t * n)) : ℕ) % n,
      Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n) = i := Fin.ext hmod
  congr 1
  funext k
  simp only [DMNCode.fbEnc, dfCode, dfRx]
  rw [hdiv, hin]
  by_cases hk : k = s₀
  · subst hk
    simp [dfSrc]
  · simp only [hk, ite_false]
    have htag : (dfTagD d₀ L₀ ε Cs B' k (getBlock (dY k)
        fun s : Fin (finProdFinEquiv (B, i) : Fin (t * n)) =>
          z ⟨s, s.2.trans (finProdFinEquiv (B, i)).2⟩ k) B : DFTag N Mm) =
        dfTagD d₀ L₀ ε Cs B' k (getBlock (dY k) fun s => z s k) B := by
      refine dfTagD_congr d₀ L₀ ε Cs B' k _ fun j' hj' => ?_
      funext i'
      have hlt : i'.val + n * j' < ((finProdFinEquiv (B, i) : Fin (t * n)) : ℕ) := by
        have hval : ((finProdFinEquiv (B, i) : Fin (t * n)) : ℕ) = i + n * B := rfl
        rw [hval]
        have h₁ : n * (j' + 1) ≤ n * B := Nat.mul_le_mul_left _ hj'
        have h₂ := i'.2
        rw [Nat.mul_add, Nat.mul_one] at h₁
        omega
      have hlt' : i'.val + n * j' < t * n := lt_trans hlt (finProdFinEquiv (B, i)).2
      simp only [getBlock, dite_eq_left hlt, dite_eq_left hlt']
    rw [htag]

end Code

/-! ### The good event -/

section Good

variable {N Mm n B' t : ℕ} {X Y : Fin N → Type*} [NeZero Mm] [NeZero n] [∀ k, Fintype (X k)]
  [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] {M : Fin N → ℕ}

omit [NeZero n] [∀ k, DecidableEq (X k)] in
/-- The tests depend only on the received sequences of the window. -/
lemma dfWin_congr_Z (d₀ : ∀ l, X l) (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ)
    (Cs : ℕ → DFBlock N Mm n X) (d : Fin N) {Zd Zd' : ℕ → Fin n → Y d} {j : ℕ} (a : ℕ → Fin Mm)
    (h : ∀ k : Fin N, (k : ℕ) < d → Zd (j + k) = Zd' (j + k)) :
    dfWin d₀ L₀ ε Cs d Zd j a ↔ dfWin d₀ L₀ ε Cs d Zd' j a := by
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  rw [h k hk]

/-- The randomness of the blocks, from the codes and the received symbols. -/
def dfSeqOf (Cst : Fin t → DFBlock N Mm n X) (z : Fin (t * n) → ∀ k, Y k) :
    Fin t → DFΞ N Mm n X Y :=
  fun B => (Cst B, nncBlocks z B)

omit [NeZero n] [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] in
/-- The received block of a node. -/
lemma getBlock_col (dY : ∀ k, Y k) (z : Fin (t * n) → ∀ k, Y k) (k : Fin N) (B : Fin t) :
    getBlock (dY k) (fun s => z s k) B = fun i => nncBlocks z B i k :=
  getBlock_nncBlocks (dY k) (fun s => z s k) B

omit [NeZero n] [∀ k, DecidableEq (X k)] in
/-- The hypotheses of the estimates of a node, on the good event. -/
lemma dfGood_win {d₀ : ∀ l, X l} {L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ} {ε : ℝ} {msg : ℕ → Fin Mm}
    (hb : B' + N ≤ t) {dξ : DFΞ N Mm n X Y} {Cst : Fin t → DFBlock N Mm n X}
    {z : Fin (t * n) → ∀ k, Y k} (hG : DFGood d₀ L₀ ε msg B' dξ (dfSeqOf Cst z)) (dY : ∀ k, Y k)
    {d : Fin N} (hd : (d : ℕ) ≠ 0) :
    (∀ j, j < B' → dfWin d₀ L₀ ε (arrOf dξ.1 Cst) d (getBlock (dY d) fun s => z s d) j msg) ∧
    ∀ j, j < B' → ∀ m, m ≠ msg j →
      ¬ dfWin d₀ L₀ ε (arrOf dξ.1 Cst) d (getBlock (dY d) fun s => z s d) j
        (Function.update msg j m) := by
  have hC : (arrOf dξ.1 Cst) = fun B => (arrOf dξ (dfSeqOf Cst z) B).1 := by
    funext i
    rw [arrOf_fst]
    rfl
  have hZ : ∀ (j : ℕ), j < B' → ∀ k : Fin N, (k : ℕ) < d →
      (getBlock (dY d) (fun s => z s d)) (j + k) =
        (fun B i => (arrOf dξ (dfSeqOf Cst z) B).2 i d) (j + k) := by
    intro j hj k hk
    have hlt : j + k < t := by
      have := k.2
      omega
    have h₁ := getBlock_col dY z d ⟨j + k, hlt⟩
    have e : arrOf dξ (dfSeqOf Cst z) (j + k) = dfSeqOf Cst z ⟨j + k, hlt⟩ :=
      arrOf_coe dξ _ ⟨j + k, hlt⟩
    simp only [e]
    exact h₁
  rw [hC]
  refine ⟨fun j hj => ?_, fun j hj m hm => ?_⟩
  · rw [dfWin_congr_Z d₀ L₀ ε _ d (Zd' := fun B i => (arrOf dξ (dfSeqOf Cst z) B).2 i d) msg
      (hZ j hj)]
    exact dfWin_true_of_good d₀ hb hG.1 d hj
  · rw [dfWin_congr_Z d₀ L₀ ε _ d (Zd' := fun B i => (arrOf dξ (dfSeqOf Cst z) B).2 i d) _
      (hZ j hj)]
    exact dfWin_wrong_of_good d₀ hG hd hj hm

omit [NeZero n] [∀ k, DecidableEq (X k)] in
/-- **On the good event, the actual run is the genie run.** -/
theorem dfRx_eq_of_good {d₀ : ∀ l, X l} {L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ} {ε : ℝ}
    {μ : Fin B' → Fin Mm} (hb : B' + N ≤ t) {dξ : DFΞ N Mm n X Y} {Cst : Fin t → DFBlock N Mm n X}
    {z : Fin (t * n) → ∀ k, Y k} (hG : DFGood d₀ L₀ ε (dfMsg μ) B' dξ (dfSeqOf Cst z))
    (dY : ∀ k, Y k) {s₀ : Fin N} (hs : (s₀ : ℕ) = 0) (B : ℕ) (i : Fin n) :
    dfRx (B' := B') d₀ L₀ ε (arrOf dξ.1 Cst) s₀ (dfMsg μ) dY z B i =
      dfX d₀ (arrOf dξ.1 Cst B) (dfTagOf (dfMsg μ) B) i := by
  funext k
  simp only [dfRx]
  by_cases hk : k = s₀
  · simp [hk]
  · have hk0 : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext (h.trans hs.symm))
    obtain ⟨h₁, h₂⟩ := dfGood_win hb hG dY hk0
    rw [ite_eq_right hk]
    exact dfX_tagD_eq_of_good d₀ L₀ ε _ (fun j hj => dfMsg_zero μ j hj) h₁ h₂ B i

omit [∀ k, DecidableEq (X k)] in
/-- **On the good event, the destinations decode.** -/
theorem dfCode_not_wrong_of_good {d₀ : ∀ l, X l} {L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ} {ε : ℝ}
    (hb : B' + N ≤ t) {dξ : DFΞ N Mm n X Y} {Cst : Fin t → DFBlock N Mm n X}
    {s₀ : Fin N} {e : Fin (M s₀) → Fin B' → Fin Mm} (he : Function.Injective e) (dY : ∀ k, Y k)
    (hM : ∀ k, 0 < M k) {D : Finset (Fin N)} (hD : ∀ k ∈ D, (k : ℕ) ≠ 0) {m : ∀ k, Fin (M k)}
    {z : Fin (t * n) → ∀ k, Y k} (hG : DFGood d₀ L₀ ε (dfMsg (e (m s₀))) B' dξ (dfSeqOf Cst z)) :
    ¬ (dfCode d₀ L₀ ε (arrOf dξ.1 Cst) s₀ e dY hM (t * n)).Wrong (mcDest s₀ D) (m, z) := by
  classical
  rintro ⟨j, k, hk, hne⟩
  have hj : j = s₀ := by
    by_contra h
    simp [mcDest, h] at hk
  subst hj
  have hkD : k ∈ D := by simpa [mcDest] using hk
  obtain ⟨h₁, h₂⟩ := dfGood_win hb hG dY (hD k hkD)
  have hest : (fun i : Fin B' => dfEst d₀ L₀ ε (arrOf dξ.1 Cst) B' k
      (getBlock (dY k) fun s => z s k) i) = e (m j) := by
    funext i
    rw [dfEst_eq_of_good d₀ L₀ ε _ (fun t ht => dfMsg_zero _ t ht) h₁ h₂ i]
    simp [dfMsg]
  apply hne
  simp only [dfCode]
  rw [hest, Function.update_self]
  have : Nonempty (Fin (M j)) := ⟨⟨0, hM j⟩⟩
  exact Function.leftInverse_invFun he (m j)

end Good

/-! ### The average error -/

section Avg

variable {N Mm n B' t : ℕ} {X Y : Fin N → Type*} [NeZero Mm] [NeZero n] [∀ k, Fintype (X k)]
  [∀ k, Fintype (Y k)] [∀ k, DecidableEq (X k)] {M : Fin N → ℕ} {p : (∀ l, X l) → ℝ}
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {κ : ∀ k, (∀ l, X l) → X k → ℝ}

/-- The law of the genie run, given the codes. -/
def dfGen (d₀ : ∀ l, X l) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (Cs : ℕ → DFBlock N Mm n X)
    (msg : ℕ → Fin Mm) (z : Fin (t * n) → ∀ k, Y k) : ℝ :=
  ∏ B : Fin t, seqChan W n (dfX d₀ (Cs B) (dfTagOf msg B)) (nncBlocks z B)

omit [NeZero n] [∀ k, Fintype (X k)] [∀ k, DecidableEq (X k)] in
lemma sum_dfGen [∀ k, Finite (X k)] (d₀ : ∀ l, X l)
    (hW : IsChannel W) (Cs : ℕ → DFBlock N Mm n X) (msg : ℕ → Fin Mm) :
    ∑ z : Fin (t * n) → ∀ k, Y k, dfGen d₀ W Cs msg z = 1 := by
  classical
  have : ∀ k, Fintype (X k) := fun k => Fintype.ofFinite _
  have h := sum_prod_pi (ι := Fin t) (A := fun _ => Fin n → ∀ k, Y k)
    fun B v => seqChan W n (dfX d₀ (Cs B) (dfTagOf msg B)) v
  simp only [(seqChan_isChannel hW n _).sum_eq_one, prod_const_one] at h
  rw [← h]
  exact Fintype.sum_equiv (nncBlockEquiv _) _ _ fun _ => rfl

omit [∀ k, DecidableEq (X k)] in
/-- The total mass of the actual run is one. -/
lemma sum_dfRx (d₀ : ∀ l, X l) (L₀ : (∀ l, X l) × (∀ l, Y l) → ℝ) (ε : ℝ) (hW : IsChannel W)
    (Cs : ℕ → DFBlock N Mm n X) (s₀ : Fin N) (e : Fin (M s₀) → Fin B' → Fin Mm) (dY : ∀ k, Y k)
    (hM : ∀ k, 0 < M k) (m : ∀ k, Fin (M k)) :
    ∑ z : Fin (t * n) → ∀ k, Y k, ∏ B : Fin t, seqChan W n
      (dfRx (B' := B') d₀ L₀ ε Cs s₀ (dfMsg (e (m s₀))) dY z B) (nncBlocks z B) = 1 := by
  classical
  have : Nonempty (∀ k, Fin (M k)) := ⟨fun k => ⟨0, hM k⟩⟩
  have hU : uniformPMF (∀ k, Fin (M k)) m ≠ 0 := by
    have hc : (0 : ℝ) < Fintype.card (∀ k, Fin (M k)) := by exact_mod_cast Fintype.card_pos
    simp only [uniformPMF]
    positivity
  have h := congrFun (dist_fst_fbLaw (ν := uniformPMF (∀ k, Fin (M k))) (W := W)
    (enc := (dfCode d₀ L₀ ε Cs s₀ e dY hM (t * n)).fbEnc) hW (t * n)) m
  simp only [dist, Fintype.sum_prod_type] at h
  rw [Finset.sum_eq_single m (fun m' _ hm' => sum_eq_zero fun z _ => by simp [hm']) (by simp)] at h
  simp only [ite_true] at h
  have hl : ∀ z, fbLaw (uniformPMF (∀ k, Fin (M k))) W
      (dfCode d₀ L₀ ε Cs s₀ e dY hM (t * n)).fbEnc (t * n) (m, z) =
      uniformPMF (∀ k, Fin (M k)) m * ∏ B : Fin t, seqChan W n
        (dfRx (B' := B') d₀ L₀ ε Cs s₀ (dfMsg (e (m s₀))) dY z B) (nncBlocks z B) :=
    fun z => dfCode_law d₀ L₀ ε Cs s₀ e dY hM m z
  simp_rw [hl, ← mul_sum] at h
  exact mul_left_cancel₀ hU (h.trans (mul_one _).symm)

set_option synthInstance.maxSize 1024 in
/-- **The average of the probability of error over the codes of the blocks.** -/
theorem dfCode_avg_le (d₀ : ∀ l, X l) (hp : IsPMF p) (hW : IsChannel W)
    (hκc : ∀ k, IsChannel (κ k))
    (hκ : ∀ k c a, dfJoint p d₀ k (c, a) = marg (dfJoint p d₀ k) c * κ k c a) (ε : ℝ)
    (hb : B' + N ≤ t) (dξ : DFΞ N Mm n X Y) {s₀ : Fin N} (hs : (s₀ : ℕ) = 0)
    {ee : Fin (M s₀) → Fin B' → Fin Mm} (hee : Function.Injective ee) (dY : ∀ k, Y k)
    (hM : ∀ k, 0 < M k) {D : Finset (Fin N)} (hD : ∀ k ∈ D, (k : ℕ) ≠ 0) {e : ℝ}
    (he : ∀ d : Fin N, (d : ℕ) ≠ 0 → exp (-(n * dfEd d₀ (jointOf p W) ε d)) ≤ e) (he0 : 0 ≤ e) :
    ∑ Cst : Fin t → DFBlock N Mm n X, piLaw (fun _ => dfBlockLaw κ Mm n) Cst *
      (dfCode d₀ (jointOf p W) ε (arrOf dξ.1 Cst) s₀ ee dY hM (t * n)).errProb W (mcDest s₀ D) ≤
    t * (1 - prob (iidPMF (jointOf p W) n) (robustTypicalSet (jointOf p W) n ε)) +
      N * (B' * (Mm * e)) := by
  classical
  set L₁ := jointOf p W with hL₁
  have : Nonempty (∀ k, Fin (M k)) := ⟨fun k => ⟨0, hM k⟩⟩
  have hU : IsPMF (uniformPMF (∀ k, Fin (M k))) := uniformPMF_isPMF
  have hν := fun B : Fin t => dfBlockLaw_isPMF (X := X) (Mm := Mm) (n := n) hκc
  set RHS := t * (1 - prob (iidPMF L₁ n) (robustTypicalSet L₁ n ε)) + N * (B' * (Mm * e)) with hRHS
  -- for one tuple of messages
  have hrow : ∀ m : ∀ k, Fin (M k), ∑ Cst : Fin t → DFBlock N Mm n X, ∑ z : Fin (t * n) → ∀ k, Y k,
      piLaw (fun _ => dfBlockLaw κ Mm n) Cst * ((∏ B : Fin t, seqChan W n
        (dfRx (B' := B') d₀ L₁ ε (arrOf dξ.1 Cst) s₀ (dfMsg (ee (m s₀))) dY z B) (nncBlocks z B)) *
        ind ((dfCode d₀ L₁ ε (arrOf dξ.1 Cst) s₀ ee dY hM (t * n)).Wrong (mcDest s₀ D) (m, z))) ≤
      RHS := by
    intro m
    set μ := ee (m s₀) with hμ
    -- for one code
    have hone : ∀ Cst : Fin t → DFBlock N Mm n X, ∑ z : Fin (t * n) → ∀ k, Y k,
        (∏ B : Fin t, seqChan W n (dfRx (B' := B') d₀ L₁ ε (arrOf dξ.1 Cst) s₀ (dfMsg μ) dY z B)
          (nncBlocks z B)) *
        ind ((dfCode d₀ L₁ ε (arrOf dξ.1 Cst) s₀ ee dY hM (t * n)).Wrong (mcDest s₀ D) (m, z)) ≤
        ∑ z : Fin (t * n) → ∀ k, Y k, dfGen d₀ W (arrOf dξ.1 Cst) (dfMsg μ) z *
          ind (¬ DFGood d₀ L₁ ε (dfMsg μ) B' dξ (dfSeqOf Cst z)) := by
      intro Cst
      set G := fun z : Fin (t * n) → ∀ k, Y k => DFGood d₀ L₁ ε (dfMsg μ) B' dξ (dfSeqOf Cst z)
        with hG
      set Rl := fun z : Fin (t * n) → ∀ k, Y k => ∏ B : Fin t, seqChan W n
        (dfRx (B' := B') d₀ L₁ ε (arrOf dξ.1 Cst) s₀ (dfMsg μ) dY z B) (nncBlocks z B) with hRl
      have hR0 : ∀ z, 0 ≤ Rl z := fun z => prod_nonneg fun B _ =>
        (seqChan_isChannel hW n _).nonneg _
      have hRs : ∑ z, Rl z = 1 := sum_dfRx d₀ L₁ ε hW _ s₀ ee dY hM m
      have hGs : ∑ z : Fin (t * n) → ∀ k, Y k, dfGen d₀ W (arrOf dξ.1 Cst) (dfMsg μ) z = 1 :=
        sum_dfGen d₀ hW _ _
      have hsplit : ∀ F : (Fin (t * n) → ∀ k, Y k) → ℝ,
          ∑ z, F z * ind (¬ G z) = ∑ z, F z - ∑ z, F z * ind (G z) := by
        intro F
        rw [eq_sub_iff_add_eq, ← sum_add_distrib]
        refine sum_congr rfl fun z _ => ?_
        by_cases hz : G z
        · rw [ind_of_neg (not_not.mpr hz), ind_of_pos hz]
          ring
        · rw [ind_of_pos hz, ind_of_neg hz]
          ring
      have heq : ∀ z, G z → Rl z = dfGen d₀ W (arrOf dξ.1 Cst) (dfMsg μ) z := by
        intro z hz
        simp only [hRl, dfGen]
        refine prod_congr rfl fun B _ => ?_
        congr 1
        funext i
        exact dfRx_eq_of_good hb hz dY hs B i
      calc _ ≤ ∑ z, Rl z * ind (¬ G z) := by
            refine sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hR0 z)
            refine ind_mono fun hw hz => ?_
            exact dfCode_not_wrong_of_good hb hee dY hM hD (m := m) hz hw
        _ = _ := by
            rw [hsplit, hsplit, hRs, hGs]
            congr 1
            refine sum_congr rfl fun z _ => ?_
            by_cases hz : G z
            · rw [heq z hz]
            · rw [ind_of_neg hz, mul_zero, mul_zero]
    -- the codes and the outputs are the randomness of the blocks
    let eq₁ : (Fin t → DFBlock N Mm n X) × (Fin (t * n) → ∀ k, Y k) ≃ (Fin t → DFΞ N Mm n X Y) :=
      (Equiv.prodCongr (Equiv.refl _) (nncBlockEquiv _)).trans
        (Equiv.arrowProdEquivProdArrow _ _ _).symm
    have hsum : ∀ F : (Fin t → DFΞ N Mm n X Y) → ℝ,
        ∑ Cst : Fin t → DFBlock N Mm n X, ∑ z : Fin (t * n) → ∀ k, Y k, F (dfSeqOf Cst z) =
          ∑ ξ, F ξ := by
      intro F
      rw [← Fintype.sum_prod_type']
      exact Fintype.sum_equiv eq₁ (fun p => F (dfSeqOf p.1 p.2)) F fun p => rfl
    have hlaw : ∀ (Cst : Fin t → DFBlock N Mm n X) (z : Fin (t * n) → ∀ k, Y k),
        piLaw (fun _ => dfBlockLaw κ Mm n) Cst * dfGen d₀ W (arrOf dξ.1 Cst) (dfMsg μ) z =
        piLaw (fun B : Fin t => dfPB d₀ κ W (dfTagOf (dfMsg μ) B)) (dfSeqOf Cst z) := by
      intro Cst z
      simp only [piLaw, dfGen, dfPB, dfSeqOf, prod_mul_distrib]
      congr 1
      refine prod_congr rfl fun B _ => ?_
      rw [arrOf_coe]
    have hgen := sum_dfGenie_not_good_le d₀ hp hW hκc hκ hb (dfMsg μ) ε dξ he he0
    calc _ ≤ ∑ Cst : Fin t → DFBlock N Mm n X, piLaw (fun _ => dfBlockLaw κ Mm n) Cst *
          ∑ z : Fin (t * n) → ∀ k, Y k, dfGen d₀ W (arrOf dξ.1 Cst) (dfMsg μ) z *
            ind (¬ DFGood d₀ L₁ ε (dfMsg μ) B' dξ (dfSeqOf Cst z)) := by
          refine sum_le_sum fun Cst _ => ?_
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left (hone Cst) (piLaw_nonneg (fun B => hν B) Cst)
      _ = ∑ Cst : Fin t → DFBlock N Mm n X, ∑ z : Fin (t * n) → ∀ k, Y k,
          piLaw (fun B : Fin t => dfPB d₀ κ W (dfTagOf (dfMsg μ) B)) (dfSeqOf Cst z) *
            ind (¬ DFGood d₀ L₁ ε (dfMsg μ) B' dξ (dfSeqOf Cst z)) := by
          refine sum_congr rfl fun Cst _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun z _ => ?_
          rw [← hlaw, mul_assoc]
      _ = ∑ ξ : Fin t → DFΞ N Mm n X Y,
          piLaw (fun B : Fin t => dfPB d₀ κ W (dfTagOf (dfMsg μ) B)) ξ *
            ind (¬ DFGood d₀ L₁ ε (dfMsg μ) B' dξ ξ) :=
          hsum fun ξ => piLaw (fun B : Fin t => dfPB d₀ κ W (dfTagOf (dfMsg μ) B)) ξ *
            ind (¬ DFGood d₀ L₁ ε (dfMsg μ) B' dξ ξ)
      _ ≤ RHS := hgen
  -- the average over the messages
  have hexp : ∑ Cst : Fin t → DFBlock N Mm n X, piLaw (fun _ => dfBlockLaw κ Mm n) Cst *
      (dfCode d₀ L₁ ε (arrOf dξ.1 Cst) s₀ ee dY hM (t * n)).errProb W (mcDest s₀ D) =
      ∑ m : ∀ k, Fin (M k), uniformPMF (∀ k, Fin (M k)) m * ∑ Cst : Fin t → DFBlock N Mm n X,
        ∑ z : Fin (t * n) → ∀ k, Y k, piLaw (fun _ => dfBlockLaw κ Mm n) Cst * ((∏ B : Fin t,
          seqChan W n (dfRx (B' := B') d₀ L₁ ε (arrOf dξ.1 Cst) s₀ (dfMsg (ee (m s₀))) dY z B)
            (nncBlocks z B)) *
          ind ((dfCode d₀ L₁ ε (arrOf dξ.1 Cst) s₀ ee dY hM (t * n)).Wrong (mcDest s₀ D) (m, z))) :=
            by
    simp only [DMNCode.errProb, Fintype.sum_prod_type, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun m _ => sum_congr rfl fun Cst _ => sum_congr rfl fun z _ => ?_
    rw [dfCode_law]
    ring
  rw [hexp]
  calc _ ≤ ∑ m : ∀ k, Fin (M k), uniformPMF (∀ k, Fin (M k)) m * RHS :=
        sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hrow m) (hU.nonneg m)
    _ = RHS := by rw [← sum_mul, hU.sum_eq_one, one_mul]

end Avg

end InfoTheory
