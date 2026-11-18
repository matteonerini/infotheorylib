/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Secrecy.WiretapExamples
public import InfoTheoryLib.Network.TwoWayLossy

/-!
# Secret key agreement: the source model and the upper bound

Theorem 8 of Lecture 23 of El Gamal and Kim. Two nodes observe i.i.d. sources `X₁ⁿ` and `X₂ⁿ`, and
an eavesdropper observes `Zⁿ`. The nodes talk over a public noiseless channel and agree on a key.
The secret key capacity is at most `min_{p(z̄ | z)} I(X₁; X₂ | Z̄)`.

## Main definitions

* `KeyCode spk M K a₁ a₂`: a protocol between nodes with the observations in `a₁` and `a₂`.
* `keyLaw P π₁ π₂ n`: the law of the sources and of the private randomness of the nodes.
* `IsAchievableKey`, `keyCapacityOf`, `keyCapacity`: the secret key capacity, in bits.

## Main statements

* `condMutualInfo_trans_le`: `I(A₁; A₂ | Mᵠ, E) ≤ I(A₁; A₂ | E)`: talking does not create
  dependence between the nodes.
* `KeyCode.entropy_key_le`: `H(K₁) ≤ I(K₁; Mᵠ, E) + I(A₁; A₂ | E) + H(K₁ | K₂)`.
* `IsAchievableKey.le`: **Theorem 8 of Lecture 23**.

## Implementation notes

The notes let the key take values in `ℤ⁺` and only ask that `P{K₁ ≠ K₂}`, the leakage rate and
`liminf H(Kⱼ) / n ≥ R` behave. Their proof of the upper bound uses Fano's inequality for
`H(K₁ | K₂)`, which needs a bound on the number of keys. With an unbounded alphabet the theorem
fails: with probability `εₙ` each node draws a huge private key, so that `H(Kⱼ) / n` is as large as
desired while `P{K₁ ≠ K₂} ≤ 2 εₙ` and the leakage is `0` (see `unbounded_key_counterexample` in the
index of Lecture 23). So the keys here take values in `[1 : 2 ^ ⌈nR⌉]`, as they do in the proof of
achievability of the notes.

A randomized encoder and a randomized key are functions of a private random variable of the node, as
the notes do on page 23-49. We allow an arbitrary order of the speakers instead of the round robin.
Rounds in which a node has nothing to say have a single index.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Independent parts -/

section Product

variable {A B a b : Type*} [Fintype A] [Fintype B] [Fintype a] [Fintype b]

/-- `H(F(A), G(B)) = H(F(A)) + H(G(B))` for independent `A` and `B`. -/
lemma entropyRV_prodDist {μ : A → ℝ} (hμ : IsPMF μ) {ρ : B → ℝ} (hρ : IsPMF ρ) (F : A → a)
    (G : B → b) :
    H[fun z => (F z.1, G z.2) ; prodDist μ ρ] = H[F ; μ] + H[G ; ρ] := by
  have hν := hμ.prodDist hρ
  have h₁ : dist (prodDist μ ρ) (fun z => F z.1) = dist μ F :=
    funext (dist_prodDist_comp_fst μ hρ F)
  have h₂ : dist (prodDist μ ρ) (fun z => G z.2) = dist ρ G :=
    funext (dist_prodDist_comp_snd hμ ρ G)
  have hI : I[(fun z : A × B => F z.1) : (fun z => G z.2) ; prodDist μ ρ] = 0 := by
    rw [mutualInfo_eq_zero_iff hν]
    intro x y
    have := dist_prodDist_pair μ ρ F G x y
    rw [h₁, h₂]
    exact this
  rw [mutualInfo_eq_add_sub hν] at hI
  have e₁ : H[(fun z : A × B => F z.1) ; prodDist μ ρ] = H[F ; μ] :=
    by rw [entropyRV, h₁, entropyRV]
  have e₂ : H[(fun z : A × B => G z.2) ; prodDist μ ρ] = H[G ; ρ] :=
    by rw [entropyRV, h₂, entropyRV]
  have e₃ : H[pair (fun z : A × B => F z.1) (fun z => G z.2) ; prodDist μ ρ] =
      H[fun z => (F z.1, G z.2) ; prodDist μ ρ] := rfl
  linarith

end Product

/-! ### Talking does not create dependence -/

section Interactive

variable {Ω a₁ a₂ ε : Type*} [Fintype Ω] [Fintype a₁] [Fintype a₂] [Fintype ε] {μ : Ω → ℝ}

/-- One round. If `M` is a function of `Y` and `T`, then `I(X; Y | M, T) ≤ I(X; Y | T)`. -/
lemma condMutualInfo_step_le {c x y m : Type*} [Fintype c] [Fintype x] [Fintype y] [Fintype m]
    (hμ : IsPMF μ) {X : Ω → x} {Y : Ω → y} {T : Ω → c} {M : Ω → m} (φ : y × c → m)
    (hM : M = φ ∘ pair Y T) : I[X : Y | pair M T ; μ] ≤ I[X : Y | T ; μ] := by
  have h₁ := chain_rule_condMutualInfo hμ X Y M T
  have h₂ : I[X : pair Y M | T ; μ] = I[X : Y | T ; μ] := by
    rw [condMutualInfo, condMutualInfo]
    congr 1
    refine (condEntropy_eq_of_comp hμ X (A := pair Y T) (B := pair (pair Y M) T)
      (fun w => ((w.1, φ w), w.2)) (fun w => (w.1.1, w.2)) ?_ rfl).symm
    funext ω
    simp only [Function.comp, pair]
    rw [hM]
    rfl
  have h₃ := condMutualInfo_nonneg hμ X M T
  linarith

variable {q : ℕ} {M : Fin q → ℕ} [∀ l, NeZero (M l)]

instance : ∀ l, Nonempty (Fin (M l)) := fun _ => ⟨0⟩

/-- **Lecture 23 of [elgamal2010], page 23-29.** A protocol for secret key agreement between nodes
with the observations `a₁` and `a₂`. In the round `l` the node `1`, if `spk l`, or the node `2`, if
not, broadcasts one of `M l` indices, a function of its observation and of the previous indices.
Each node generates a key from its observation and the indices. -/
structure KeyCode {q : ℕ} (spk : Fin q → Bool) (M : Fin q → ℕ) (K : ℕ) (a₁ a₂ : Type*) where
  /-- The index of the round `l`, if the speaker is node `1`. -/
  enc₁ : ∀ l, a₁ → (∀ l', Fin (M l')) → Fin (M l)
  /-- The index of the round `l`, if the speaker is node `2`. -/
  enc₂ : ∀ l, a₂ → (∀ l', Fin (M l')) → Fin (M l)
  /-- The key of node `1`. -/
  key₁ : a₁ → (∀ l', Fin (M l')) → Fin K
  /-- The key of node `2`. -/
  key₂ : a₂ → (∀ l', Fin (M l')) → Fin K

variable {spk : Fin q → Bool} {K : ℕ}

namespace KeyCode

/-- The protocol, for the given observations. -/
def protocol (c : KeyCode spk M K a₁ a₂) (x₁ : a₁) (x₂ : a₂) (l : Fin q)
    (h : ∀ l', Fin (M l')) : Fin (M l) :=
  if spk l then c.enc₁ l x₁ h else c.enc₂ l x₂ h

/-- The transcript `Mᵠ`, for the given observations. -/
def trans (c : KeyCode spk M K a₁ a₂) (x₁ : a₁) (x₂ : a₂) : ∀ l, Fin (M l) :=
  run (c.protocol x₁ x₂)

variable (c : KeyCode spk M K a₁ a₂)

/-- **Page 23-47 of [elgamal2010]: `I(A₁; A₂ | M^{r+1}, E) ≤ I(A₁; A₂ | Mʳ, E)`.** So the mutual
information of the observations given the first `r` indices is at most the one given no index. -/
theorem condMutualInfo_runTo_le (hμ : IsPMF μ) (A₁ : Ω → a₁) (A₂ : Ω → a₂) (E : Ω → ε) (r : ℕ)
    (hr : r ≤ q) :
    I[A₁ : A₂ | pair (fun ω => runTo (c.protocol (A₁ ω) (A₂ ω)) r) E ; μ] ≤ I[A₁ : A₂ | E ; μ] := by
  classical
  induction r with
  | zero =>
    refine le_of_eq (condMutualInfo_congr_comp (Z := pair (fun ω => runTo
      (c.protocol (A₁ ω) (A₂ ω)) 0) E) (Z' := E) hμ A₁ A₂ (fun w => w.2)
      (fun w => ((fun _ => Classical.arbitrary _), w)) rfl ?_)
    funext ω
    rfl
  | succ r ih =>
    have hlt : r < q := hr
    set l : Fin q := ⟨r, hlt⟩ with hl
    refine le_trans ?_ (ih (by omega))
    set Hist := fun ω => runTo (c.protocol (A₁ ω) (A₂ ω)) r with hHist
    set T := pair Hist E with hT
    set Mn : Ω → Fin (M l) := fun ω => c.protocol (A₁ ω) (A₂ ω) l (Hist ω) with hMn
    have hnext : I[A₁ : A₂ | pair Mn T ; μ] ≤ I[A₁ : A₂ | T ; μ] := by
      by_cases hs : spk l = true
      · have h := condMutualInfo_step_le hμ (X := A₂) (Y := A₁) (T := T) (M := Mn)
          (fun w => c.enc₁ l w.1 w.2.1) (by
            funext ω
            simp [hMn, protocol, hs, pair, hT])
        rwa [condMutualInfo_comm hμ, condMutualInfo_comm hμ A₂] at h
      · have hs' : spk l = false := by simpa using hs
        exact condMutualInfo_step_le hμ (X := A₁) (Y := A₂) (T := T) (M := Mn)
          (fun w => c.enc₂ l w.1 w.2.1) (by
            funext ω
            simp [hMn, protocol, hs', pair, hT])
    refine le_trans (le_of_eq ?_) hnext
    refine (condMutualInfo_congr_comp hμ _ _
      (fun w : (∀ l', Fin (M l')) × ε => (w.1 l, Function.update w.1 l (Classical.arbitrary _),
        w.2))
      (fun w => (Function.update w.2.1 l w.1, w.2.2)) ?_ ?_)
    · funext ω
      have h₁ := runTo_succ_comm (fun ω => c.protocol (A₁ ω) (A₂ ω)) r hlt ω
      have h₂ : Function.update (runTo (c.protocol (A₁ ω) (A₂ ω)) (r + 1)) l
          (Classical.arbitrary _) = Hist ω := by
        rw [h₁]
        funext l'
        by_cases hl' : l' = l
        · subst hl'
          simp only [Function.update_self, hHist]
          exact (runTo_of_le _ (le_refl r)).symm
        · rw [Function.update_of_ne hl', Function.update_of_ne hl']
      simp only [Function.comp, pair]
      refine Prod.ext ?_ (Prod.ext h₂.symm rfl)
      change Mn ω = runTo (c.protocol (A₁ ω) (A₂ ω)) (r + 1) l
      rw [h₁, Function.update_self]
    · funext ω
      have h₁ := runTo_succ_comm (fun ω => c.protocol (A₁ ω) (A₂ ω)) r hlt ω
      simp only [Function.comp, pair]
      exact Prod.ext h₁ rfl

/-- `I(A₁; A₂ | Mᵠ, E) ≤ I(A₁; A₂ | E)`. -/
theorem condMutualInfo_trans_le (hμ : IsPMF μ) (A₁ : Ω → a₁) (A₂ : Ω → a₂) (E : Ω → ε) :
    I[A₁ : A₂ | pair (fun ω => c.trans (A₁ ω) (A₂ ω)) E ; μ] ≤ I[A₁ : A₂ | E ; μ] :=
  c.condMutualInfo_runTo_le hμ A₁ A₂ E q le_rfl

/-- **Pages 23-45 and 23-46 of [elgamal2010], with randomization in the observations.** For an
eavesdropper with the observation `E`, `H(K₁) ≤ I(K₁; Mᵠ, E) + I(A₁; A₂ | E) + H(K₁ | K₂)`. -/
theorem entropy_key_le (hμ : IsPMF μ) (A₁ : Ω → a₁) (A₂ : Ω → a₂) (E : Ω → ε) :
    H[fun ω => c.key₁ (A₁ ω) (c.trans (A₁ ω) (A₂ ω)) ; μ] ≤
      I[(fun ω => c.key₁ (A₁ ω) (c.trans (A₁ ω) (A₂ ω))) :
        pair (fun ω => c.trans (A₁ ω) (A₂ ω)) E ; μ] +
      I[A₁ : A₂ | E ; μ] +
      H[(fun ω => c.key₁ (A₁ ω) (c.trans (A₁ ω) (A₂ ω))) |
        (fun ω => c.key₂ (A₂ ω) (c.trans (A₁ ω) (A₂ ω))) ; μ] := by
  set T := fun ω => c.trans (A₁ ω) (A₂ ω) with hT
  set K₁ := fun ω => c.key₁ (A₁ ω) (T ω) with hK₁
  set K₂ := fun ω => c.key₂ (A₂ ω) (T ω) with hK₂
  set C := pair T E with hC
  have h₁ := mutualInfo_eq_entropy_sub_condEntropy hμ K₁ C
  have h₂ : I[K₁ : A₂ | C ; μ] = H[K₁ | C ; μ] - H[K₁ | pair A₂ C ; μ] := rfl
  have h₃ : H[K₁ | pair A₂ C ; μ] ≤ H[K₁ | K₂ ; μ] :=
    condEntropy_le_condEntropy_comp hμ K₁ (pair A₂ C) fun w => c.key₂ w.1 w.2.1
  have h₄ : I[K₁ : A₂ | C ; μ] ≤ I[A₁ : A₂ | C ; μ] := by
    have e₁ : I[A₂ : pair A₁ C | C ; μ] = I[A₂ : A₁ | C ; μ] := by
      rw [condMutualInfo, condMutualInfo]
      congr 1
      exact (condEntropy_eq_of_comp hμ A₂ (A := pair A₁ C) (B := pair (pair A₁ C) C)
        (fun w => (w, w.2)) (fun w => w.1) rfl rfl).symm
    have e₂ := condMutualInfo_comp_le hμ A₂ (pair A₁ C) C fun w => c.key₁ w.1 w.2.1
    rw [e₁] at e₂
    rw [condMutualInfo_comm hμ K₁, condMutualInfo_comm hμ A₁]
    exact e₂
  have h₅ := c.condMutualInfo_trans_le hμ A₁ A₂ E
  linarith

end KeyCode

end Interactive

/-! ### The block law -/

section Block

variable {ξ κ : Type*} [Fintype ξ] [Fintype κ]

/-- The law of an i.i.d. sequence and of an independent random variable. -/
def secBlockLaw (P : ξ → ℝ) (ρ : κ → ℝ) (n : ℕ) : (Fin n → ξ) × κ → ℝ := prodDist (iidPMF P n) ρ

lemma secBlockLaw_isPMF {P : ξ → ℝ} (hP : IsPMF P) {ρ : κ → ℝ} (hρ : IsPMF ρ) (n : ℕ) :
    IsPMF (secBlockLaw P ρ n) :=
  (iidPMF_isPMF hP n).prodDist hρ

/-- The entropy of a letterwise function and of a function of the independent part. -/
lemma entropy_blockLaw {a b : Type*} [Fintype a] [Fintype b] {P : ξ → ℝ} (hP : IsPMF P)
    {ρ : κ → ℝ} (hρ : IsPMF ρ) (n : ℕ) (f : ξ → a) (g : κ → b) :
    H[fun w => ((fun i => f (w.1 i)), g w.2) ; secBlockLaw P ρ n] = n * H[f ; P] + H[g ; ρ] := by
  have h := entropyRV_prodDist (iidPMF_isPMF hP n) hρ (fun (ω : Fin n → ξ) i => f (ω i)) g
  rw [entropyRV_iidPMF_comp hP n f] at h
  exact h

/-- The entropy of a block, up to an injective relabeling. -/
lemma entropy_blockLaw_of {a b c : Type*} [Fintype a] [Fintype b] [Fintype c] {P : ξ → ℝ}
    (hP : IsPMF P) {ρ : κ → ℝ} (hρ : IsPMF ρ) (n : ℕ) (f : ξ → a) (g : κ → b)
    (Y : (Fin n → ξ) × κ → c) (e : (Fin n → a) × b → c) (he : Function.Injective e)
    (hY : ∀ w, Y w = e ((fun i => f (w.1 i)), g w.2)) :
    H[Y ; secBlockLaw P ρ n] = n * H[f ; P] + H[g ; ρ] := by
  rw [← entropy_blockLaw hP hρ n f g]
  exact entropyRV_eq_of_injective _ e he hY

end Block

/-! ### Codes on sources -/

section Sources

variable {α₁ α₂ γ κ₁ κ₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype γ] [Fintype κ₁] [Fintype κ₂]

/-- The law of `n` letters of a source and of the private random variables of the nodes. -/
def keyLaw {ξ : Type*} (P : ξ → ℝ) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) (n : ℕ) :
    (Fin n → ξ) × κ₁ × κ₂ → ℝ := secBlockLaw P (prodDist π₁ π₂) n

variable {q n : ℕ} {spk : Fin q → Bool} {M : Fin q → ℕ} [∀ l, NeZero (M l)] {K : ℕ}

/-- The observation of node `1`: `(X₁ⁿ, W₁)`. -/
def obs₁ {ξ : Type*} (f : ξ → α₁) (w : (Fin n → ξ) × κ₁ × κ₂) : (Fin n → α₁) × κ₁ :=
  (fun i => f (w.1 i), w.2.1)

/-- The observation of node `2`: `(X₂ⁿ, W₂)`. -/
def obs₂ {ξ : Type*} (f : ξ → α₂) (w : (Fin n → ξ) × κ₁ × κ₂) : (Fin n → α₂) × κ₂ :=
  (fun i => f (w.1 i), w.2.2)

/-- The source has letters `(x₁, x₂, z)`. -/
abbrev srcLetter (α₁ α₂ γ : Type*) := α₁ × α₂ × γ

namespace KeyCode

variable (c : KeyCode spk M K ((Fin n → α₁) × κ₁) ((Fin n → α₂) × κ₂))

/-- The transcript `Mᵠ`, on the block. -/
def transB {ξ : Type*} (f₁ : ξ → α₁) (f₂ : ξ → α₂) (w : (Fin n → ξ) × κ₁ × κ₂) : ∀ l, Fin (M l) :=
  c.trans (obs₁ f₁ w) (obs₂ f₂ w)

/-- The key `K₁`, on the block. -/
def keyB₁ {ξ : Type*} (f₁ : ξ → α₁) (f₂ : ξ → α₂) (w : (Fin n → ξ) × κ₁ × κ₂) : Fin K :=
  c.key₁ (obs₁ f₁ w) (c.transB f₁ f₂ w)

/-- The key `K₂`, on the block. -/
def keyB₂ {ξ : Type*} (f₁ : ξ → α₁) (f₂ : ξ → α₂) (w : (Fin n → ξ) × κ₁ × κ₂) : Fin K :=
  c.key₂ (obs₂ f₂ w) (c.transB f₁ f₂ w)

/-- **Page 23-29 of [elgamal2010].** The probability of error `P{K₁ ≠ K₂}`. -/
def errProbB (P : srcLetter α₁ α₂ γ → ℝ) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) : ℝ :=
  InfoTheory.errProb (keyLaw P π₁ π₂ n) (c.keyB₁ Prod.fst fun a => a.2.1)
    (c.keyB₂ Prod.fst fun a => a.2.1) id

/-- The sequence `Zⁿ`, on the block. -/
def eveB (w : (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂) : Fin n → γ := fun i => (w.1 i).2.2

/-- **Page 23-29 of [elgamal2010].** The leakage `I(K₁; Zⁿ, Mᵠ)`. -/
def leak₁ (P : srcLetter α₁ α₂ γ → ℝ) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) : ℝ :=
  I[c.keyB₁ Prod.fst fun a => a.2.1 :
    pair eveB (c.transB Prod.fst fun a => a.2.1) ; keyLaw P π₁ π₂ n]

/-- **Page 23-29 of [elgamal2010].** The leakage `I(K₂; Zⁿ, Mᵠ)`. -/
def leak₂ (P : srcLetter α₁ α₂ γ → ℝ) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) : ℝ :=
  I[c.keyB₂ Prod.fst fun a => a.2.1 :
    pair eveB (c.transB Prod.fst fun a => a.2.1) ; keyLaw P π₁ π₂ n]

/-- The entropy `H(K₁)`. -/
def entropyKey₁ (P : srcLetter α₁ α₂ γ → ℝ) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) : ℝ :=
  H[c.keyB₁ Prod.fst fun a => a.2.1 ; keyLaw P π₁ π₂ n]

/-- The entropy `H(K₂)`. -/
def entropyKey₂ (P : srcLetter α₁ α₂ γ → ℝ) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) : ℝ :=
  H[c.keyB₂ Prod.fst fun a => a.2.1 ; keyLaw P π₁ π₂ n]

end KeyCode

/-- **Page 23-30 of [elgamal2010].** A secret key rate `R`, in bits, is achievable with the
protocols in `allowed` if for every `ε` and all large `n` there is a protocol with keys in
`[1 : 2 ^ ⌈nR⌉]`, with probability of error at most `ε`, leakage rate at most `ε`, and
`H(Kⱼ) ≥ n (R - ε)`. The nodes have private random variables, with any finite alphabets. -/
def IsAchievableKey (allowed : ∀ q, (Fin q → Bool) → Prop) (P : srcLetter α₁ α₂ γ → ℝ) (R : ℝ) :
    Prop :=
  0 ≤ R ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (q : ℕ) (spk : Fin q → Bool) (M : Fin q → ℕ)
    (_ : ∀ l, NeZero (M l)) (κ₁ κ₂ : Type) (_ : Fintype κ₁) (_ : Fintype κ₂) (π₁ : κ₁ → ℝ)
    (π₂ : κ₂ → ℝ) (c : KeyCode spk M (2 ^ ⌈n * R⌉₊) ((Fin n → α₁) × κ₁) ((Fin n → α₂) × κ₂)),
    allowed q spk ∧ IsPMF π₁ ∧ IsPMF π₂ ∧ c.errProbB P π₁ π₂ ≤ ε ∧
      c.leak₁ P π₁ π₂ ≤ n * ε ∧ c.leak₂ P π₁ π₂ ≤ n * ε ∧
      n * (R * log 2 - ε) ≤ c.entropyKey₁ P π₁ π₂ ∧ n * (R * log 2 - ε) ≤ c.entropyKey₂ P π₁ π₂

/-- The secret key capacity with the protocols in `allowed`, in bits. -/
def keyCapacityOf (allowed : ∀ q, (Fin q → Bool) → Prop) (P : srcLetter α₁ α₂ γ → ℝ) : ℝ :=
  sSup {R | IsAchievableKey allowed P R}

/-- **Page 23-30 of [elgamal2010].** The secret key capacity `C_K(X₁; X₂ ‖ Z)`, in bits. -/
def keyCapacity (P : srcLetter α₁ α₂ γ → ℝ) : ℝ := keyCapacityOf (fun _ _ => True) P

/-! ### The upper bound -/

/-- `I(X₁; X₂ | Z̄)`, for `Z̄` from `Z` through the channel `Q`. -/
def intrinsicInfoOf {γ' : Type*} [Fintype γ'] (P : srcLetter α₁ α₂ γ → ℝ) (Q : γ → γ' → ℝ) : ℝ :=
  I[(fun a : srcLetter α₁ α₂ γ × γ' => a.1.1) : (fun a => a.1.2.1) | Prod.snd ;
    jointOf P fun a => Q a.2.2]

variable {γ' : Type*} [Fintype γ'] {P : srcLetter α₁ α₂ γ → ℝ} {Q : γ → γ' → ℝ}

/-- The extended source, with the letter of `Z̄`. -/
abbrev extSource (P : srcLetter α₁ α₂ γ → ℝ) (Q : γ → γ' → ℝ) : srcLetter α₁ α₂ γ × γ' → ℝ :=
  jointOf P fun a => Q a.2.2

/-- The map from the block of the extended source to the block of the source. -/
def dropExt (w : (Fin n → srcLetter α₁ α₂ γ × γ') × κ₁ × κ₂) :
    (Fin n → srcLetter α₁ α₂ γ) × κ₁ × κ₂ := (fun i => (w.1 i).1, w.2)

/-- The block law of the source is the image of the block law of the extended source. -/
lemma dist_dropExt (hQ : IsChannel Q) (π₁ : κ₁ → ℝ) (π₂ : κ₂ → ℝ) :
    dist (keyLaw (extSource P Q) π₁ π₂ n) dropExt = keyLaw P π₁ π₂ n := by
  have hQ' : IsChannel fun a : srcLetter α₁ α₂ γ => Q a.2.2 := fun a => hQ _
  funext ⟨ω, u⟩
  have h := dist_prodDist_pair (iidPMF (extSource P Q) n) (prodDist π₁ π₂)
    (fun (v : Fin n → srcLetter α₁ α₂ γ × γ') i => (v i).1) id ω u
  have e₁ : dist (iidPMF (extSource P Q) n) (fun v i => (v i).1) = iidPMF P n := by
    rw [dist_iidPMF_comp, dist_jointOf_fst hQ']
  have e₂ : dist (prodDist π₁ π₂) id u = prodDist π₁ π₂ u := by rw [dist_id]
  rw [e₁, e₂] at h
  exact h

variable {π₁ : κ₁ → ℝ} {π₂ : κ₂ → ℝ}

/-- The entropies of the private random variables add up. -/
lemma entropy_seeds (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) :
    H[id ; prodDist π₁ π₂] = H[Prod.fst ; prodDist π₁ π₂] + H[Prod.snd ; prodDist π₁ π₂] := by
  have h := entropyRV_prodDist hπ₁ hπ₂ (id : κ₁ → κ₁) (id : κ₂ → κ₂)
  have e₁ : H[Prod.fst ; prodDist π₁ π₂] = H[id ; π₁] := by
    rw [entropyRV, entropyRV]
    congr 1
    exact funext (dist_prodDist_comp_fst π₁ hπ₂ id)
  have e₂ : H[Prod.snd ; prodDist π₁ π₂] = H[id ; π₂] := by
    rw [entropyRV, entropyRV]
    congr 1
    exact funext (dist_prodDist_comp_snd hπ₁ π₂ id)
  rw [e₁, e₂, ← h]
  rfl

/-- A constant has entropy `0`, for the seeds. -/
lemma entropy_seeds_const (hρ : IsPMF (prodDist π₁ π₂)) :
    H[(fun _ => ()) ; prodDist π₁ π₂] = 0 :=
  entropyRV_const hρ ()

section Generic

variable {ξ a b c : Type*} [Fintype ξ] [Fintype a] [Fintype b] [Fintype c] {P₀ : ξ → ℝ}

/-- The entropy of a block for the law of the source and of the private random variables. -/
lemma entropy_keyLaw_of {d e' f' : Type*} [Fintype d] [Fintype e'] [Fintype f'] (hP : IsPMF P₀)
    (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) (n : ℕ) (f : ξ → d) (g : κ₁ × κ₂ → e')
    (Y : (Fin n → ξ) × κ₁ × κ₂ → f') (em : (Fin n → d) × e' → f') (he : Function.Injective em)
    (hY : ∀ w, Y w = em ((fun i => f (w.1 i)), g w.2)) :
    H[Y ; keyLaw P₀ π₁ π₂ n] = n * H[f ; P₀] + H[g ; prodDist π₁ π₂] :=
  entropy_blockLaw_of hP (hπ₁.prodDist hπ₂) n f g Y em he hY

/-- The observations of the nodes have `I(A₁; A₂ | Eⁿ) = n I(X₁; X₂ | E)`. -/
lemma condMutualInfo_obs_generic (hP : IsPMF P₀) (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) (x₁ : ξ → a)
    (x₂ : ξ → b) (e : ξ → c) :
    I[obs₁ (κ₂ := κ₂) (n := n) x₁ : obs₂ (κ₁ := κ₁) x₂ | (fun w i => e (w.1 i)) ;
      keyLaw P₀ π₁ π₂ n] = n * I[x₁ : x₂ | e ; P₀] := by
  have hμ : IsPMF (keyLaw P₀ π₁ π₂ n) := secBlockLaw_isPMF hP (hπ₁.prodDist hπ₂) n
  rw [condMutualInfo_eq hμ, condMutualInfo_eq hP]
  have h₁ := entropy_keyLaw_of hP hπ₁ hπ₂ n (pair e x₁) Prod.fst
    (pair (fun w i => e (w.1 i)) (obs₁ (κ₂ := κ₂) (n := n) x₁))
    (fun v => (fun i => (v.1 i).1, (fun i => (v.1 i).2, v.2)))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (congrFun h.1 i) (congrFun h.2.1 i)) h.2.2)
    fun w => rfl
  have h₂ := entropy_keyLaw_of hP hπ₁ hπ₂ n (pair e x₂) Prod.snd
    (pair (fun w i => e (w.1 i)) (obs₂ (κ₁ := κ₁) (n := n) x₂))
    (fun v => (fun i => (v.1 i).1, (fun i => (v.1 i).2, v.2)))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (congrFun h.1 i) (congrFun h.2.1 i)) h.2.2)
    fun w => rfl
  have h₃ := entropy_keyLaw_of hP hπ₁ hπ₂ n e (fun _ => ())
    (fun w i => e (w.1 i)) (fun v => v.1) (fun a b h => Prod.ext h rfl) fun w => rfl
  have h₄ := entropy_keyLaw_of hP hπ₁ hπ₂ n (pair e (pair x₁ x₂)) id
    (pair (fun w i => e (w.1 i)) (pair (obs₁ (κ₂ := κ₂) (n := n) x₁) (obs₂ (κ₁ := κ₁) x₂)))
    (fun v => (fun i => (v.1 i).1, ((fun i => (v.1 i).2.1, v.2.1), (fun i => (v.1 i).2.2, v.2.2))))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (congrFun h.1 i)
        (Prod.ext (congrFun h.2.1.1 i) (congrFun h.2.2.1 i))) (Prod.ext h.2.1.2 h.2.2.2))
    fun w => rfl
  have h₅ := entropy_seeds hπ₁ hπ₂
  have h₆ := entropy_seeds_const (hπ₁.prodDist hπ₂)
  rw [h₁, h₂, h₃, h₄, h₅, h₆]
  ring

/-- A letterwise function and the private random variables with another one, given a third:
`I(Fⁿ; (Gⁿ, W) | Hⁿ) = n I(F; G | H)`. -/
lemma condMutualInfo_seeds_generic (hP : IsPMF P₀) (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) (f : ξ → a)
    (g : ξ → b) (e : ξ → c) :
    I[(fun w : (Fin n → ξ) × κ₁ × κ₂ => (fun i => f (w.1 i) : Fin n → a)) :
      (fun w => ((fun i => g (w.1 i) : Fin n → b), w.2)) | (fun w i => e (w.1 i)) ;
      keyLaw P₀ π₁ π₂ n] = n * I[f : g | e ; P₀] := by
  have hμ : IsPMF (keyLaw P₀ π₁ π₂ n) := secBlockLaw_isPMF hP (hπ₁.prodDist hπ₂) n
  rw [condMutualInfo_eq hμ, condMutualInfo_eq hP]
  have h₁ := entropy_keyLaw_of hP hπ₁ hπ₂ n (pair e f) (fun _ => ())
    (pair (fun w i => e (w.1 i)) fun w i => f (w.1 i))
    (fun v => (fun i => (v.1 i).1, fun i => (v.1 i).2))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (congrFun h.1 i) (congrFun h.2 i)) rfl)
    fun w => rfl
  have h₂ := entropy_keyLaw_of hP hπ₁ hπ₂ n (pair e g) id
    (pair (fun w i => e (w.1 i)) fun w => ((fun i => g (w.1 i) : Fin n → b), w.2))
    (fun v => (fun i => (v.1 i).1, ((fun i => (v.1 i).2), v.2)))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (congrFun h.1 i) (congrFun h.2.1 i)) h.2.2)
    fun w => rfl
  have h₃ := entropy_keyLaw_of hP hπ₁ hπ₂ n e (fun _ => ())
    (fun w i => e (w.1 i)) (fun v => v.1) (fun a b h => Prod.ext h rfl) fun w => rfl
  have h₄ := entropy_keyLaw_of hP hπ₁ hπ₂ n (pair e (pair f g)) id
    (pair (fun w i => e (w.1 i)) (pair (fun w i => f (w.1 i))
      fun w => ((fun i => g (w.1 i) : Fin n → b), w.2)))
    (fun v => (fun i => (v.1 i).1, ((fun i => (v.1 i).2.1), ((fun i => (v.1 i).2.2), v.2))))
    (fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (funext fun i => Prod.ext (congrFun h.1 i)
        (Prod.ext (congrFun h.2.1 i) (congrFun h.2.2.1 i))) h.2.2.2)
    fun w => rfl
  have h₆ := entropy_seeds_const (hπ₁.prodDist hπ₂)
  rw [h₁, h₂, h₃, h₄, h₆]
  ring

end Generic

/-- **Page 23-48 of [elgamal2010]: the eavesdropper can only degrade.** `Z̄` is independent of
`(X₁, X₂)` given `Z`. -/
lemma condMutualInfo_ext_letter (hP : IsPMF P) (hQ : IsChannel Q) :
    I[(Prod.snd : srcLetter α₁ α₂ γ × γ' → γ') : (fun a => (a.1.1, a.1.2.1)) | (fun a => a.1.2.2) ;
      extSource P Q] = 0 := by
  have hQ' : IsChannel fun a : srcLetter α₁ α₂ γ => Q a.2.2 := fun a => hQ _
  have hPb : IsPMF (extSource P Q) := jointOf_isPMF hP hQ'
  have e₃ : H[(Prod.snd : srcLetter α₁ α₂ γ × γ' → γ') | pair (fun a => a.1.2.2)
      (fun a => (a.1.1, a.1.2.1)) ; extSource P Q] =
      H[Prod.snd | Prod.fst ; extSource P Q] :=
    condEntropy_congr_right hPb _ (fun a => (a.2.2, a.1, a.2.1))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 (Prod.ext h.2.2 h.1)) fun _ => rfl
  have e₄ := condEntropy_jointOf_comp hP hQ (fun a : srcLetter α₁ α₂ γ => a.2.2)
  rw [condMutualInfo_eq' hPb, e₃]
  exact sub_eq_zero.2 e₄.symm

/-- **Page 23-48 of [elgamal2010].** On the block of the extended source, the observations have
`I(A₁; A₂ | Z̄ⁿ) = n I(X₁; X₂ | Z̄)`. -/
lemma condMutualInfo_obs_eq (hP : IsPMF P) (hQ : IsChannel Q) (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) :
    I[obs₁ (κ₂ := κ₂) (n := n) (fun a : srcLetter α₁ α₂ γ × γ' => a.1.1) :
      obs₂ (κ₁ := κ₁) (fun a : srcLetter α₁ α₂ γ × γ' => a.1.2.1) |
      (fun w i => (w.1 i).2) ; keyLaw (extSource P Q) π₁ π₂ n] =
      n * intrinsicInfoOf P Q := by
  have hQ' : IsChannel fun a : srcLetter α₁ α₂ γ => Q a.2.2 := fun a => hQ _
  exact condMutualInfo_obs_generic (jointOf_isPMF hP hQ') hπ₁ hπ₂ _ _ Prod.snd

/-- **Page 23-48 of [elgamal2010].** On the block of the extended source,
`I(Z̄ⁿ; (X₁ⁿ, X₂ⁿ, W₁, W₂) | Zⁿ) = 0`. -/
lemma condMutualInfo_ext_eq_zero (hP : IsPMF P) (hQ : IsChannel Q) (hπ₁ : IsPMF π₁)
    (hπ₂ : IsPMF π₂) :
    I[(fun w : (Fin n → srcLetter α₁ α₂ γ × γ') × κ₁ × κ₂ => (fun i => (w.1 i).2 : Fin n → γ')) :
      (fun w => ((fun i => ((w.1 i).1.1, (w.1 i).1.2.1) : Fin n → α₁ × α₂), w.2)) |
      (fun w i => (w.1 i).1.2.2) ; keyLaw (extSource P Q) π₁ π₂ n] = 0 := by
  have hQ' : IsChannel fun a : srcLetter α₁ α₂ γ => Q a.2.2 := fun a => hQ _
  have h := condMutualInfo_seeds_generic (n := n) (jointOf_isPMF hP hQ') hπ₁ hπ₂
    (Prod.snd : srcLetter α₁ α₂ γ × γ' → γ') (fun a => (a.1.1, a.1.2.1)) (fun a => a.1.2.2)
  rw [condMutualInfo_ext_letter hP hQ, mul_zero] at h
  exact h

variable {q n : ℕ} {spk : Fin q → Bool} {M : Fin q → ℕ} [∀ l, NeZero (M l)] {K : ℕ}

/-- **Pages 23-45 to 23-48 of [elgamal2010]: the bound of Theorem 8 for one code.**
`H(K₁) ≤ I(K₁; Zⁿ, Mᵠ) + n I(X₁; X₂ | Z̄) + log 2 + Pₑ log K`. -/
theorem KeyCode.entropyKey₁_le (c : KeyCode spk M K ((Fin n → α₁) × κ₁) ((Fin n → α₂) × κ₂))
    (hP : IsPMF P) (hQ : IsChannel Q) (hπ₁ : IsPMF π₁) (hπ₂ : IsPMF π₂) :
    c.entropyKey₁ P π₁ π₂ ≤ c.leak₁ P π₁ π₂ + n * intrinsicInfoOf P Q + log 2 +
      c.errProbB P π₁ π₂ * log K := by
  have hQ' : IsChannel fun a : srcLetter α₁ α₂ γ => Q a.2.2 := fun a => hQ _
  have hPb : IsPMF (extSource P Q) := jointOf_isPMF hP hQ'
  have hμ : IsPMF (keyLaw (extSource P Q) π₁ π₂ n) := secBlockLaw_isPMF hPb (hπ₁.prodDist hπ₂) n
  have hμ₀ : IsPMF (keyLaw P π₁ π₂ n) := secBlockLaw_isPMF hP (hπ₁.prodDist hπ₂) n
  have hd := dist_dropExt (n := n) (P := P) hQ π₁ π₂
  set x₁ : srcLetter α₁ α₂ γ × γ' → α₁ := fun a => a.1.1
  set x₂ : srcLetter α₁ α₂ γ × γ' → α₂ := fun a => a.1.2.1
  set Φ := dropExt (α₁ := α₁) (α₂ := α₂) (γ := γ) (γ' := γ') (κ₁ := κ₁) (κ₂ := κ₂) (n := n)
  set K₁ := c.keyB₁ (Prod.fst : srcLetter α₁ α₂ γ → α₁) fun a => a.2.1
  set K₂ := c.keyB₂ (Prod.fst : srcLetter α₁ α₂ γ → α₁) fun a => a.2.1
  set T := c.transB (Prod.fst : srcLetter α₁ α₂ γ → α₁) fun a => a.2.1
  set Z := KeyCode.eveB (α₁ := α₁) (α₂ := α₂) (γ := γ) (κ₁ := κ₁) (κ₂ := κ₂) (n := n)
  set E : (Fin n → srcLetter α₁ α₂ γ × γ') × κ₁ × κ₂ → Fin n → γ' := fun w i => (w.1 i).2
  have h := c.entropy_key_le hμ (obs₁ (κ₂ := κ₂) x₁) (obs₂ (κ₁ := κ₁) x₂) E
  -- Back to the law of the source.
  have e₁ : H[K₁ ∘ Φ ; keyLaw (extSource P Q) π₁ π₂ n] = H[K₁ ; keyLaw P π₁ π₂ n] := by
    rw [← hd, entropyRV, entropyRV, dist_comp_eq]
  have e₂ : H[K₁ ∘ Φ | K₂ ∘ Φ ; keyLaw (extSource P Q) π₁ π₂ n] = H[K₁ | K₂ ; keyLaw P π₁ π₂ n] :=
    by
    refine condEntropy_eq_of_dist_pair_eq hμ hμ₀ ?_
    rw [← hd, ← dist_comp_eq]
    rfl
  have e₃ : I[K₁ ∘ Φ : pair (Z ∘ Φ) (T ∘ Φ) ; keyLaw (extSource P Q) π₁ π₂ n] =
      I[K₁ : pair Z T ; keyLaw P π₁ π₂ n] := by
    refine mutualInfo_eq_of_dist_pair_eq ?_
    rw [← hd, ← dist_comp_eq]
    rfl
  have e₄ := condMutualInfo_obs_eq (n := n) hP hQ hπ₁ hπ₂ (κ₁ := κ₁) (κ₂ := κ₂)
  -- The eavesdropper can only degrade.
  have hdeg : I[K₁ ∘ Φ : pair (T ∘ Φ) E ; keyLaw (extSource P Q) π₁ π₂ n] ≤
      I[K₁ ∘ Φ : pair (Z ∘ Φ) (T ∘ Φ) ; keyLaw (extSource P Q) π₁ π₂ n] := by
    set D : (Fin n → srcLetter α₁ α₂ γ × γ') × κ₁ × κ₂ → (Fin n → α₁ × α₂) × κ₁ × κ₂ :=
      fun w => ((fun i => ((w.1 i).1.1, (w.1 i).1.2.1)), w.2) with hD
    have h₀ := condMutualInfo_ext_eq_zero (n := n) hP hQ hπ₁ hπ₂ (κ₁ := κ₁) (κ₂ := κ₂)
    have h₁ := condMutualInfo_comp_le hμ E D (Z ∘ Φ)
      (fun v => (c.key₁ (fun i => (v.1 i).1, v.2.1) (c.trans (fun i => (v.1 i).1, v.2.1)
        (fun i => (v.1 i).2, v.2.2)), c.trans (fun i => (v.1 i).1, v.2.1)
        (fun i => (v.1 i).2, v.2.2)))
    have h₂ : (I[E : D | Z ∘ Φ ; keyLaw (extSource P Q) π₁ π₂ n]) = 0 := h₀
    have h₃ := chain_rule_condMutualInfo hμ E (K₁ ∘ Φ) (T ∘ Φ) (Z ∘ Φ)
    have h₄ := condMutualInfo_nonneg hμ E (T ∘ Φ) (Z ∘ Φ)
    have h₅ := condMutualInfo_nonneg hμ E (K₁ ∘ Φ) (pair (T ∘ Φ) (Z ∘ Φ))
    have h₆ : I[E : pair (K₁ ∘ Φ) (T ∘ Φ) | Z ∘ Φ ; keyLaw (extSource P Q) π₁ π₂ n] ≤ 0 := by
      rw [← h₂]
      exact h₁
    have h₇ : I[K₁ ∘ Φ : E | pair (T ∘ Φ) (Z ∘ Φ) ; keyLaw (extSource P Q) π₁ π₂ n] = 0 := by
      rw [condMutualInfo_comm hμ]
      linarith
    have h₈ := chain_rule_mutualInfo₂ hμ (K₁ ∘ Φ) E (pair (T ∘ Φ) (Z ∘ Φ))
    have h₉ := mutualInfo_comp_le hμ (K₁ ∘ Φ) (pair E (pair (T ∘ Φ) (Z ∘ Φ)))
      (fun v => (v.2.1, v.1))
    have h₁₀ : I[K₁ ∘ Φ : pair (T ∘ Φ) (Z ∘ Φ) ; keyLaw (extSource P Q) π₁ π₂ n] =
        I[K₁ ∘ Φ : pair (Z ∘ Φ) (T ∘ Φ) ; keyLaw (extSource P Q) π₁ π₂ n] :=
      mutualInfo_congr_right hμ _ Prod.swap Prod.swap_injective fun _ => rfl |>.symm
    have h₁₁ : I[K₁ ∘ Φ : (fun v => (v.2.1, v.1)) ∘ pair E (pair (T ∘ Φ) (Z ∘ Φ)) ;
        keyLaw (extSource P Q) π₁ π₂ n] = I[K₁ ∘ Φ : pair (T ∘ Φ) E ;
        keyLaw (extSource P Q) π₁ π₂ n] := rfl
    linarith
  -- Fano's inequality.
  have hF := fano_weak hμ₀ K₁ K₂ id
  rw [Fintype.card_fin] at hF
  have h₁ : H[(fun ω => c.key₁ (obs₁ x₁ ω) (c.trans (obs₁ x₁ ω) (obs₂ x₂ ω))) ;
      keyLaw (extSource P Q) π₁ π₂ n] = H[K₁ ∘ Φ ; keyLaw (extSource P Q) π₁ π₂ n] := rfl
  have h₂ : H[(fun ω => c.key₁ (obs₁ x₁ ω) (c.trans (obs₁ x₁ ω) (obs₂ x₂ ω))) |
      (fun ω => c.key₂ (obs₂ x₂ ω) (c.trans (obs₁ x₁ ω) (obs₂ x₂ ω))) ;
      keyLaw (extSource P Q) π₁ π₂ n] = H[K₁ ∘ Φ | K₂ ∘ Φ ; keyLaw (extSource P Q) π₁ π₂ n] := rfl
  have h₃ : I[(fun ω => c.key₁ (obs₁ x₁ ω) (c.trans (obs₁ x₁ ω) (obs₂ x₂ ω))) :
      pair (fun ω => c.trans (obs₁ x₁ ω) (obs₂ x₂ ω)) E ; keyLaw (extSource P Q) π₁ π₂ n] =
      I[K₁ ∘ Φ : pair (T ∘ Φ) E ; keyLaw (extSource P Q) π₁ π₂ n] := rfl
  rw [h₁, h₂, h₃, e₁, e₂, e₄] at h
  have e₅ : c.entropyKey₁ P π₁ π₂ = H[K₁ ; keyLaw P π₁ π₂ n] := rfl
  have e₆ : c.leak₁ P π₁ π₂ = I[K₁ : pair Z T ; keyLaw P π₁ π₂ n] := rfl
  have e₇ : c.errProbB P π₁ π₂ = InfoTheory.errProb (keyLaw P π₁ π₂ n) K₁ K₂ id := rfl
  rw [e₅, e₆, e₇]
  linarith

/-- **Theorem 8 of Lecture 23 of [elgamal2010], page 23-45.** For every channel `p(z̄ | z)`, an
achievable secret key rate is at most `I(X₁; X₂ | Z̄)`. -/
theorem IsAchievableKey.le {allowed : ∀ q, (Fin q → Bool) → Prop} {R : ℝ}
    (h : IsAchievableKey allowed P R) (hP : IsPMF P) (hQ : IsChannel Q) :
    R * log 2 ≤ intrinsicInfoOf P Q := by
  have hl := log_pos one_lt_two
  have ha : 0 ≤ R * log 2 := mul_nonneg h.1 hl.le
  refine le_of_forall_eventually_mul_le ha fun ε' hε' => ?_
  refine ⟨2 * log 2, ?_⟩
  set ε := min (ε' / 2) 1 with hε
  have hε0 : 0 < ε := lt_min (by linarith) one_pos
  have hε₁ : ε ≤ ε' / 2 := min_le_left _ _
  have hε₂ : ε ≤ 1 := min_le_right _ _
  filter_upwards [h.2 ε hε0] with n hn
  obtain ⟨q, spk, M, hM, κ₁, κ₂, _, _, π₁, π₂, c, -, hπ₁, hπ₂, herr, hl₁, -, hk₁, -⟩ := hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb := c.entropyKey₁_le hP hQ hπ₁ hπ₂
  have hlogK := log_two_pow_ceil_le n h.1
  have hlogK0 : 0 ≤ log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) := log_natCast_nonneg _
  have h₁ : c.errProbB P π₁ π₂ * log ((2 ^ ⌈n * R⌉₊ : ℕ) : ℝ) ≤ ε * (n * (R * log 2) + log 2) :=
    (mul_le_mul_of_nonneg_right herr hlogK0).trans (mul_le_mul_of_nonneg_left hlogK hε0.le)
  have hA : 0 ≤ (n : ℝ) * (R * log 2) := mul_nonneg hn0 ha
  have h₂ : ε * (n * (R * log 2)) ≤ ε' * (n * (R * log 2)) := by
    refine mul_le_mul_of_nonneg_right ?_ hA
    linarith
  have h₃ : ε * log 2 ≤ log 2 := by nlinarith
  have h₄ : (n : ℝ) * (ε + ε) ≤ n * ε' := mul_le_mul_of_nonneg_left (by linarith) hn0
  have e₁ : (n : ℝ) * (R * log 2 - ε) = n * (R * log 2) - n * ε := by ring
  have e₂ : (n : ℝ) * (intrinsicInfoOf P Q + ε') = n * intrinsicInfoOf P Q + n * ε' := by ring
  have e₃ : (1 - ε') * ((n : ℝ) * (R * log 2)) = n * (R * log 2) - ε' * (n * (R * log 2)) := by ring
  have e₄ : ε * (n * (R * log 2) + log 2) = ε * (n * (R * log 2)) + ε * log 2 := by ring
  have e₅ : (n : ℝ) * (ε + ε) = n * ε + n * ε := by ring
  rw [e₂, e₃]
  linarith

/-- **Page 23-48 of [elgamal2010].** The infimum over the channels `p(z̄ | z)` of `I(X₁; X₂ | Z̄)`.
The notes write a minimum, with no bound on the alphabet of `Z̄`. -/
def intrinsicInfo (P : srcLetter α₁ α₂ γ → ℝ) : ℝ :=
  sInf {v | ∃ (k : ℕ) (Q : γ → Fin k → ℝ), IsChannel Q ∧ intrinsicInfoOf P Q = v}

omit [Fintype κ₁] [Fintype κ₂] in
/-- `I(X₁; X₂ | Z̄)` is nonnegative. -/
lemma intrinsicInfoOf_nonneg (hP : IsPMF P) (hQ : IsChannel Q) : 0 ≤ intrinsicInfoOf P Q := by
  have hQ' : IsChannel fun a : srcLetter α₁ α₂ γ => Q a.2.2 := fun a => hQ _
  exact condMutualInfo_nonneg (jointOf_isPMF hP hQ') _ _ _

/-- **Theorem 8 of Lecture 23 of [elgamal2010], page 23-45.** The secret key capacity is at most the
infimum over the channels `p(z̄ | z)` of `I(X₁; X₂ | Z̄)`, in bits. -/
theorem keyCapacity_le (allowed : ∀ q, (Fin q → Bool) → Prop) (hP : IsPMF P) :
    keyCapacityOf allowed P ≤ intrinsicInfo P / log 2 := by
  have hl := log_pos one_lt_two
  have hne : {v | ∃ (k : ℕ) (Q : γ → Fin k → ℝ), IsChannel Q ∧ intrinsicInfoOf P Q = v}.Nonempty :=
    by
    refine ⟨_, 1, fun _ _ => 1, fun _ => ⟨fun _ => zero_le_one, by simp⟩, rfl⟩
  have hnn : 0 ≤ intrinsicInfo P := by
    refine le_csInf hne ?_
    rintro _ ⟨k, Q, hQ, rfl⟩
    exact intrinsicInfoOf_nonneg hP hQ
  refine Real.sSup_le (fun R hR => ?_) (div_nonneg hnn hl.le)
  rw [le_div_iff₀ hl]
  refine le_csInf hne ?_
  rintro _ ⟨k, Q, hQ, rfl⟩
  exact hR.le hP hQ

/-- **Theorem 8 of Lecture 23 of [elgamal2010], page 23-47.** For any channel `Q` from `Z` to `Z̄`,
the secret key capacity is at most `I(X₁; X₂ | Z̄)`; with `Z̄ = Z` this is `I(X₁; X₂ | Z)`. -/
theorem keyCapacity_le_of_channel (allowed : ∀ q, (Fin q → Bool) → Prop) (hP : IsPMF P)
    (hQ : IsChannel Q) : keyCapacityOf allowed P ≤ intrinsicInfoOf P Q / log 2 := by
  have hl := log_pos one_lt_two
  refine Real.sSup_le (fun R hR => ?_) (div_nonneg (intrinsicInfoOf_nonneg hP hQ) hl.le)
  rw [le_div_iff₀ hl]
  exact hR.le hP hQ

end Sources

end InfoTheory
