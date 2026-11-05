/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MDTriangle
public import InfoTheoryLib.Network.TwoWayRelay

/-!
# Two-way lossy source coding: codes and the Markov chains

Theorem 4 of Lecture 21 of El Gamal and Kim, due to Kaspi. Two nodes observe `X₁ⁿ` and `X₂ⁿ` and
exchange indices in `q` rounds, and each node reconstructs the source of the other one.

## Main definitions

* `KaspiCode spk M n α₁ α₂ β₁ β₂`: a code. In the round `l` the node 1 speaks if `spk l`, and the
  node 2 otherwise. The notes have alternating speakers.
* `IsAchievableKaspi`, `kaspiRegion`: the `q`-round rate–distortion region.
* `IsKaspiLaw`, `kaspiInner`: the region of Theorem 4.

## Main statements

* `lemma1`, `lemma1_speak`: **Lemma 1 of page 21-25**.
* `condMutualInfo_of_indep`: the starting point of Lemma 1.
* `mutualInfo_iid_split`: disjoint sets of letters are independent.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

universe u

variable {α₁ α₂ : Type u} {β₁ β₂ : Type*}

/-- **Lecture 21 of [elgamal2010], pages 21-13 and 21-20.** A code for two-way lossy source coding
with `q` rounds. All the rounds have an encoder at both nodes, and the speaker `spk l` selects the
one that is used. -/
structure KaspiCode {q : ℕ} (spk : Fin q → Bool) (M : Fin q → ℕ) (n : ℕ)
    (α₁ α₂ β₁ β₂ : Type*) where
  /-- The encoder of node 1. -/
  enc₁ : ∀ l, (Fin n → α₁) → (∀ l', Fin (M l')) → Fin (M l)
  /-- The encoder of node 2. -/
  enc₂ : ∀ l, (Fin n → α₂) → (∀ l', Fin (M l')) → Fin (M l)
  /-- The estimate of `X₁ⁿ` at node 2. -/
  dec₁ : (Fin n → α₂) → (∀ l', Fin (M l')) → Fin n → β₁
  /-- The estimate of `X₂ⁿ` at node 1. -/
  dec₂ : (Fin n → α₁) → (∀ l', Fin (M l')) → Fin n → β₂

namespace KaspiCode

variable {q : ℕ} {spk : Fin q → Bool} {M : Fin q → ℕ} [∀ l, NeZero (M l)] {n : ℕ}

instance : ∀ l, Nonempty (Fin (M l)) := fun _ => ⟨0⟩

/-- One round of the protocol. -/
def step (c : KaspiCode spk M n α₁ α₂ β₁ β₂) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) (l : Fin q)
    (h : ∀ l', Fin (M l')) : Fin (M l) :=
  if spk l then c.enc₁ l x₁ h else c.enc₂ l x₂ h

/-- The transcript. -/
def trans (c : KaspiCode spk M n α₁ α₂ β₁ β₂) (x₁ : Fin n → α₁) (x₂ : Fin n → α₂) :
    ∀ l, Fin (M l) :=
  run (c.step x₁ x₂)

variable [Fintype α₁] [Fintype α₂]

/-- The expected distortion of the estimate of `X₁ⁿ`. -/
def distortion₁ (c : KaspiCode spk M n α₁ α₂ β₁ β₂) (P : α₁ × α₂ → ℝ) (d₁ : α₁ → β₁ → ℝ) : ℝ :=
  ∑ ω : Fin n → α₁ × α₂, iidPMF P n ω * seqDistortion d₁ (fun i => (ω i).1)
    (c.dec₁ (fun i => (ω i).2) (c.trans (fun i => (ω i).1) fun i => (ω i).2))

/-- The expected distortion of the estimate of `X₂ⁿ`. -/
def distortion₂ (c : KaspiCode spk M n α₁ α₂ β₁ β₂) (P : α₁ × α₂ → ℝ) (d₂ : α₂ → β₂ → ℝ) : ℝ :=
  ∑ ω : Fin n → α₁ × α₂, iidPMF P n ω * seqDistortion d₂ (fun i => (ω i).2)
    (c.dec₂ (fun i => (ω i).1) (c.trans (fun i => (ω i).1) fun i => (ω i).2))

end KaspiCode

variable [Fintype α₁] [Fintype α₂]

/-- **Lecture 21 of [elgamal2010], page 21-20.** A rate pair, in bits, is achievable in the rounds
of `spk` at the distortions `(D₁, D₂)` if for every `ε` and all large `n` there is a code with
distortions at most `Dⱼ + ε`. -/
def IsAchievableKaspi {q : ℕ} (P : α₁ × α₂ → ℝ) (spk : Fin q → Bool) (d₁ : α₁ → β₁ → ℝ)
    (d₂ : α₂ → β₂ → ℝ) (D₁ D₂ : ℝ) (R : ℝ × ℝ) : Prop :=
  0 ≤ R.1 ∧ 0 ≤ R.2 ∧ ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (M : Fin q → ℕ) (_ : ∀ l, NeZero (M l))
    (c : KaspiCode spk M n α₁ α₂ β₁ β₂),
    ∏ l with spk l = true, M l ≤ 2 ^ ⌊n * R.1⌋₊ ∧ ∏ l with spk l = false, M l ≤ 2 ^ ⌊n * R.2⌋₊ ∧
      c.distortion₁ P d₁ ≤ D₁ + ε ∧ c.distortion₂ P d₂ ≤ D₂ + ε

/-- **Lecture 21 of [elgamal2010], page 21-20.** The `q`-round rate–distortion region. -/
def kaspiRegion {q : ℕ} (P : α₁ × α₂ → ℝ) (spk : Fin q → Bool) (d₁ : α₁ → β₁ → ℝ)
    (d₂ : α₂ → β₂ → ℝ) (D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  closure {R | IsAchievableKaspi P spk d₁ d₂ D₁ D₂ R}

/-! ### The laws of Theorem 4 -/

section Law

variable {q : ℕ} {υ : Type*} [Fintype υ] [Nonempty υ]

open Classical in
/-- The past `U^{r-1}`: the auxiliary letters of the rounds before `r`, the others being replaced by
a default letter. -/
def truncU (r : ℕ) (u : Fin q → υ) : Fin q → υ :=
  fun l => if (l : ℕ) < r then u l else Classical.arbitrary υ

/-- **Theorem 4 of Lecture 21 of [elgamal2010], page 21-22.** A law of `(X₁, X₂, U^q)`: the law of
the sources is `P` and `p(u^q | x₁, x₂) = ∏ₗ p(uₗ | u^{l-1}, x_{jₗ})`, in the form of the Markov
chains `X_{j'} → (X_{j}, U^{l-1}) → Uₗ`, for the speaker `j` and the other node `j'` of the round
`l`. -/
structure IsKaspiLaw (P : α₁ × α₂ → ℝ) (spk : Fin q → Bool) (μ : α₁ × α₂ × (Fin q → υ) → ℝ) :
    Prop where
  /-- It is a law. -/
  isPMF : IsPMF μ
  /-- The law of the sources. -/
  marg : dist μ (fun z => (z.1, z.2.1)) = P
  /-- The Markov chains of the rounds of node 1. -/
  markov₁ : ∀ l, spk l = true →
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 l |
      pair (fun z => z.1) (fun z => truncU l z.2.2) ; μ] = 0
  /-- The Markov chains of the rounds of node 2. -/
  markov₂ : ∀ l, spk l = false →
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 l |
      pair (fun z => z.2.1) (fun z => truncU l z.2.2) ; μ] = 0

end Law

/-- **Theorem 4 of Lecture 21 of [elgamal2010], page 21-22: the region.** The rate pairs with
`R₁ ≥ I(X₁; U^q | X₂)` and `R₂ ≥ I(X₂; U^q | X₁)`, in bits, for some law and reconstructions with
the prescribed distortions. The alphabet of `U` is any finite set. -/
def kaspiInner {q : ℕ} (P : α₁ × α₂ → ℝ) (spk : Fin q → Bool) (d₁ : α₁ → β₁ → ℝ)
    (d₂ : α₂ → β₂ → ℝ) (D₁ D₂ : ℝ) : Set (ℝ × ℝ) :=
  {R | ∃ (υ : Type u) (_ : Fintype υ) (_ : Nonempty υ) (μ : α₁ × α₂ × (Fin q → υ) → ℝ)
    (f₁ : (Fin q → υ) → α₂ → β₁) (f₂ : (Fin q → υ) → α₁ → β₂), IsKaspiLaw P spk μ ∧
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.1 : fun z => z.2.2 | fun z => z.2.1 ; μ] ≤
      R.1 * log 2 ∧
    I[fun z : α₁ × α₂ × (Fin q → υ) => z.2.1 : fun z => z.2.2 | fun z => z.1 ; μ] ≤
      R.2 * log 2 ∧
    ∑ z, μ z * d₁ z.1 (f₁ z.2.2 z.2.1) ≤ D₁ ∧ ∑ z, μ z * d₂ z.2.1 (f₂ z.2.2 z.1) ≤ D₂}

/-! ### Lemma 1 -/

section Lemma1

variable {Ω a₁ a₂ b₁ b₂ : Type*} [Fintype Ω] [Fintype a₁] [Fintype a₂] [Fintype b₁] [Fintype b₂]
  {μ : Ω → ℝ}

/-- `I(A₂; B₁ | A₁, B₂) = 0` when `(A₁, B₁)` and `(A₂, B₂)` are independent. -/
theorem condMutualInfo_of_indep (hμ : IsPMF μ) {A₁ : Ω → a₁} {A₂ : Ω → a₂} {B₁ : Ω → b₁}
    {B₂ : Ω → b₂} (h : I[pair B₁ A₁ : pair A₂ B₂ ; μ] = 0) :
    I[A₂ : B₁ | pair A₁ B₂ ; μ] = 0 := by
  have h₁ := chain_rule_mutualInfo₂ hμ (pair B₁ A₁) A₂ B₂
  have h₂ := mutualInfo_nonneg hμ (pair B₁ A₁) B₂
  have h₃ := condMutualInfo_nonneg hμ (pair B₁ A₁) A₂ B₂
  have h₄ : I[pair B₁ A₁ : A₂ | B₂ ; μ] = 0 := by linarith
  rw [condMutualInfo_comm hμ] at h₄
  have h₅ := chain_rule_condMutualInfo hμ A₂ B₁ A₁ B₂
  have h₆ := condMutualInfo_nonneg hμ A₂ A₁ B₂
  have h₇ := condMutualInfo_nonneg hμ A₂ B₁ (pair A₁ B₂)
  linarith

variable {q : ℕ} {A : Fin q → Type*} [∀ l, Fintype (A l)] [∀ l, Nonempty (A l)]

/-- Conditioning on variables that are functions of each other is the same. -/
lemma condMutualInfo_congr_comp {c d x y : Type*} [Fintype c] [Fintype d] [Fintype x] [Fintype y]
    (hμ : IsPMF μ) (X : Ω → x) (Y : Ω → y) {Z : Ω → c} {Z' : Ω → d} (f : c → d) (g : d → c)
    (hf : Z' = f ∘ Z) (hg : Z = g ∘ Z') : I[X : Y | Z ; μ] = I[X : Y | Z' ; μ] := by
  rw [condMutualInfo, condMutualInfo,
    condEntropy_eq_of_comp hμ X f g hf hg,
    condEntropy_eq_of_comp hμ X (A := pair Y Z) (B := pair Y Z') (Prod.map id f) (Prod.map id g)
      (by rw [hf]; rfl) (by nth_rw 1 [hg]; rfl)]

/-- The protocol, with node 1 using `(A₁, A₂)` and node 2 using `(B₁, B₂)`. -/
def lemProtocol (spk : Fin q → Bool) (g₁ : ∀ l, a₁ × a₂ → (∀ l', A l') → A l)
    (g₂ : ∀ l, b₁ × b₂ → (∀ l', A l') → A l) (A₁ : Ω → a₁) (A₂ : Ω → a₂) (B₁ : Ω → b₁)
    (B₂ : Ω → b₂) (ω : Ω) (l : Fin q) (h : ∀ l', A l') : A l :=
  if spk l then g₁ l (A₁ ω, A₂ ω) h else g₂ l (B₁ ω, B₂ ω) h

variable {spk : Fin q → Bool} {g₁ : ∀ l, a₁ × a₂ → (∀ l', A l') → A l}
  {g₂ : ∀ l, b₁ × b₂ → (∀ l', A l') → A l} {A₁ : Ω → a₁} {A₂ : Ω → a₂} {B₁ : Ω → b₁} {B₂ : Ω → b₂}

omit [Fintype Ω] [(l : Fin q) → Fintype (A l)] in
/-- The round `r` of the protocol from the past: the pair of a new index and the past. -/
lemma runTo_succ_comm (g : Ω → ∀ l, (∀ l', A l') → A l) (r : ℕ) (hr : r < q) (ω : Ω) :
    runTo (g ω) (r + 1) = Function.update (runTo (g ω) r) ⟨r, hr⟩
      (g ω ⟨r, hr⟩ (runTo (g ω) r)) := by
  classical
  funext l
  simp only [runTo]
  by_cases h : (l : ℕ) = r
  · have e : l = ⟨r, hr⟩ := Fin.ext h
    subst e
    simp
  · have e : l ≠ ⟨r, hr⟩ := fun h' => h (by rw [h'])
    simp [h, e]

/-- One step of Lemma 1. -/
private lemma lemma1_step_info {c x y m : Type*} [Fintype c] [Fintype x] [Fintype y] [Fintype m]
    (hμ : IsPMF μ) {X : Ω → x} {Y : Ω → y} {T : Ω → c} {M : Ω → m} (φ : y × c → m)
    (hM : M = φ ∘ pair Y T) (h : I[X : Y | T ; μ] = 0) :
    I[X : M | T ; μ] = 0 ∧ I[X : Y | pair M T ; μ] = 0 := by
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
  have h₄ := condMutualInfo_nonneg hμ X Y (pair M T)
  constructor <;> linarith

/-- **Lemma 1 of page 21-25 of [elgamal2010].** `I(A₂; B₁ | Mʳ, A₁, B₂) = 0`, for all `r`. -/
theorem lemma1 (hμ : IsPMF μ) (h0 : I[A₂ : B₁ | pair A₁ B₂ ; μ] = 0) (r : ℕ) (hr : r ≤ q) :
    I[A₂ : B₁ | pair (fun ω => runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) r) (pair A₁ B₂) ; μ]
      = 0 := by
  classical
  induction r with
  | zero =>
    rw [← h0]
    refine (condMutualInfo_congr_comp hμ _ _ (fun w => w.2)
      (fun w => ((fun _ => Classical.arbitrary _), w)) rfl ?_)
    funext ω
    rfl
  | succ r ih =>
    have hlt : r < q := hr
    set l : Fin q := ⟨r, hlt⟩ with hl
    have ih' := ih (by omega)
    set Hist := fun ω => runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) r with hHist
    set T := pair Hist (pair A₁ B₂) with hT
    set M : Ω → A l := fun ω => lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω l (Hist ω) with hM
    have hnext : I[A₂ : B₁ | pair M T ; μ] = 0 := by
      by_cases hs : spk l = true
      · have := (lemma1_step_info hμ (X := B₁) (Y := A₂) (T := T) (M := M)
          (fun w => g₁ l (w.2.2.1, w.1) w.2.1) (by
            funext ω
            simp [hM, lemProtocol, hs, pair, hT]) (by
            rw [condMutualInfo_comm hμ]
            exact ih')).2
        rwa [condMutualInfo_comm hμ]
      · have hs' : spk l = false := by simpa using hs
        exact (lemma1_step_info hμ (X := A₂) (Y := B₁) (T := T) (M := M)
          (fun w => g₂ l (w.1, w.2.2.2) w.2.1) (by
            funext ω
            simp [hM, lemProtocol, hs', pair, hT]) ih').2
    rw [← hnext]
    refine condMutualInfo_congr_comp hμ _ _
      (fun w : (∀ l', A l') × a₁ × b₂ => (w.1 l, Function.update w.1 l (Classical.arbitrary _),
        w.2))
      (fun w => (Function.update w.2.1 l w.1, w.2.2)) ?_ ?_
    · funext ω
      have h₁ := runTo_succ_comm (fun ω => lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) r hlt ω
      have h₂ : Function.update (runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) (r + 1)) l
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
      change M ω = runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) (r + 1) l
      rw [h₁, Function.update_self]
    · funext ω
      have h₁ := runTo_succ_comm (fun ω => lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) r hlt ω
      simp only [Function.comp, pair]
      refine Prod.ext ?_ rfl
      exact h₁

/-- **Lemma 1 of page 21-25 of [elgamal2010], the other two statements.** The index of a round of
node 1 gives no information on `B₁`, and the index of a round of node 2 gives no information on
`A₂`. -/
theorem lemma1_speak (hμ : IsPMF μ) (h0 : I[A₂ : B₁ | pair A₁ B₂ ; μ] = 0) (l : Fin q) :
    (spk l = true → I[B₁ : fun ω => lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω l
        (runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) l) |
      pair (fun ω => runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) l) (pair A₁ B₂) ; μ] = 0) ∧
    (spk l = false → I[A₂ : fun ω => lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω l
        (runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) l) |
      pair (fun ω => runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) l) (pair A₁ B₂) ; μ] = 0) := by
  have ih := lemma1 (spk := spk) (g₁ := g₁) (g₂ := g₂) hμ h0 l l.2.le
  constructor
  · intro hs
    exact (lemma1_step_info hμ (X := B₁) (Y := A₂)
      (T := pair (fun ω => runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) l) (pair A₁ B₂))
      (fun w => g₁ l (w.2.2.1, w.1) w.2.1) (by
        funext ω
        simp [lemProtocol, hs, pair]) (by
        rw [condMutualInfo_comm hμ]
        exact ih)).1
  · intro hs
    exact (lemma1_step_info hμ (X := A₂) (Y := B₁)
      (T := pair (fun ω => runTo (lemProtocol spk g₁ g₂ A₁ A₂ B₁ B₂ ω) l) (pair A₁ B₂))
      (fun w => g₂ l (w.1, w.2.2.2) w.2.1) (by
        funext ω
        simp [lemProtocol, hs, pair]) ih).1

end Lemma1

/-! ### Independence of the letters before and after a time -/

section Split

variable {γ : Type*} [Fintype γ] {P : γ → ℝ} {n : ℕ}

/-- **Disjoint sets of letters are independent.** For functions `F` of the letters in `p` and `G` of
the others, `E(F G) = E(F) E(G)`. -/
lemma sum_iidPMF_mul_split (hP : IsPMF P) (p : Fin n → Prop) {f g : (Fin n → γ) → ℝ}
    (hf : ∀ ω ω', (∀ i, p i → ω i = ω' i) → f ω = f ω')
    (hg : ∀ ω ω', (∀ i, ¬ p i → ω i = ω' i) → g ω = g ω') :
    ∑ ω, iidPMF P n ω * (f ω * g ω) =
      (∑ ω, iidPMF P n ω * f ω) * ∑ ω, iidPMF P n ω * g ω := by
  classical
  obtain ⟨z₀⟩ : Nonempty γ := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  let e : (Fin n → γ) ≃ ({i // p i} → γ) × ({i // ¬ p i} → γ) :=
    Equiv.piEquivPiSubtypeProd p fun _ => γ
  set w₁ : ({i // p i} → γ) → ℝ := fun a => ∏ i, P (a i) with hw₁
  set w₂ : ({i // ¬ p i} → γ) → ℝ := fun b => ∏ i, P (b i) with hw₂
  have hw₁1 : ∑ a, w₁ a = 1 := by
    simp only [hw₁]
    rw [← Fintype.prod_sum fun (_ : {i // p i}) x => P x]
    simp [hP.sum_eq_one]
  have hw₂1 : ∑ b, w₂ b = 1 := by
    simp only [hw₂]
    rw [← Fintype.prod_sum fun (_ : {i // ¬ p i}) x => P x]
    simp [hP.sum_eq_one]
  have hiid : ∀ a b, iidPMF P n (e.symm (a, b)) = w₁ a * w₂ b := fun a b => by
    simp only [iidPMF, hw₁, hw₂]
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    congr 1
    · refine prod_congr rfl fun i _ => ?_
      simp [e, Equiv.piEquivPiSubtypeProd, i.2]
    · refine prod_congr rfl fun i _ => ?_
      simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  set F : ({i // p i} → γ) → ℝ := fun a => f (e.symm (a, fun _ => z₀)) with hF
  set G : ({i // ¬ p i} → γ) → ℝ := fun b => g (e.symm (fun _ => z₀, b)) with hG
  have hfF : ∀ a b, f (e.symm (a, b)) = F a := fun a b => hf _ _ fun i hi => by
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hgG : ∀ a b, g (e.symm (a, b)) = G b := fun a b => hg _ _ fun i hi => by
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hsum : ∀ h : (Fin n → γ) → ℝ, ∑ ω, iidPMF P n ω * h ω =
      ∑ a, ∑ b, w₁ a * w₂ b * h (e.symm (a, b)) := fun h => by
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by rw [hiid]
  rw [hsum, hsum, hsum]
  simp only [hfF, hgG]
  have h₁ : ∑ a, ∑ b, w₁ a * w₂ b * F a = ∑ a, w₁ a * F a := by
    refine sum_congr rfl fun a _ => ?_
    calc ∑ b, w₁ a * w₂ b * F a = (∑ b, w₂ b) * (w₁ a * F a) := by
          rw [sum_mul]
          exact sum_congr rfl fun b _ => by ring
      _ = _ := by rw [hw₂1, one_mul]
  have h₂ : ∑ a, ∑ b, w₁ a * w₂ b * G b = ∑ b, w₂ b * G b := by
    rw [sum_comm]
    refine sum_congr rfl fun b _ => ?_
    calc ∑ a, w₁ a * w₂ b * G b = (∑ a, w₁ a) * (w₂ b * G b) := by
          rw [sum_mul]
          exact sum_congr rfl fun a _ => by ring
      _ = _ := by rw [hw₁1, one_mul]
  rw [h₁, h₂, sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- `I(F; G) = 0` for a function `F` of the letters in `p` and a function `G` of the others. -/
theorem mutualInfo_iid_split {a b : Type*} [Fintype a] [Fintype b] (hP : IsPMF P)
    (p : Fin n → Prop) {F : (Fin n → γ) → a} {G : (Fin n → γ) → b}
    (hF : ∀ ω ω', (∀ i, p i → ω i = ω' i) → F ω = F ω')
    (hG : ∀ ω ω', (∀ i, ¬ p i → ω i = ω' i) → G ω = G ω') :
    I[F : G ; iidPMF P n] = 0 := by
  classical
  refine (mutualInfo_eq_zero_iff (iidPMF_isPMF hP n) F G).2 fun x y => ?_
  have h := sum_iidPMF_mul_split hP p (f := fun ω => if F ω = x then 1 else 0)
    (g := fun ω => if G ω = y then 1 else 0)
    (fun ω ω' h => by simp only [hF ω ω' h]) (fun ω ω' h => by simp only [hG ω ω' h])
  have e₁ : dist (iidPMF P n) (pair F G) (x, y) = ∑ ω, iidPMF P n ω *
      ((if F ω = x then 1 else 0) * (if G ω = y then 1 else 0)) := by
    simp only [dist, pair, Prod.mk.injEq]
    refine sum_congr rfl fun ω _ => ?_
    by_cases h₁ : F ω = x <;> by_cases h₂ : G ω = y <;> simp [h₁, h₂]
  have e₂ : dist (iidPMF P n) F x = ∑ ω, iidPMF P n ω * (if F ω = x then 1 else 0) := by
    simp only [dist]
    exact sum_congr rfl fun ω _ => by split_ifs <;> simp
  have e₃ : dist (iidPMF P n) G y = ∑ ω, iidPMF P n ω * (if G ω = y then 1 else 0) := by
    simp only [dist]
    exact sum_congr rfl fun ω _ => by split_ifs <;> simp
  rw [e₁, e₂, e₃, h]

end Split

end InfoTheory
