/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.TwoWayLossyLetters

/-!
# Two-way lossy source coding: the converse of Kaspi's theorem

The converse of Theorem 4 of Lecture 21 of El Gamal and Kim, on pages 21-24 to 21-29.

## Main definitions

* `KaspiCode.kU`: the auxiliary letter.

## Main statements

* `exists_estimator_le`: an estimator can drop a variable that is conditionally independent of the
  source.
* `condEntropy_le_sum_of_order`: the chain rule, for conditioning variables that know the earlier
  letters.
* `KaspiCode.exists_kaspi_law`: the single-letter bounds for one code.
* `exists_kaspiInner_of_mem_kaspiRegion`: **the converse of Theorem 4**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Two general tools -/

section Tools

variable {Ω a κ σ β : Type*} [Fintype Ω] [Fintype a] [Fintype κ] [Fintype σ] [Fintype β]
  [Nonempty β] {ν : Ω → ℝ}

omit [Fintype β] in
/-- **Claim (a) of page 21-25 of [elgamal2010].** If `X → C → B` is a Markov chain, a reconstruction
from `(C, B)` can be replaced by one from `C` with no larger expected distortion. The distortion may
depend on `C` as well as on `X`. -/
theorem exists_estimator_le [Finite β] (hν : IsPMF ν) (X : Ω → a) (C : Ω → κ) (B : Ω → σ)
    (g : κ × σ → β) (d : a → κ → β → ℝ) (h : I[X : B | C ; ν] = 0) : ∃ f : κ → β, ∑ ω, ν ω *
    d (X ω) (C ω) (f (C ω)) ≤ ∑ ω, ν ω * d (X ω) (C ω) (g (C ω, B ω)) := by
  have := Fintype.ofFinite β
  classical
  have hlaw := (condIndep_iff_dist_eq hν X B C).1 ((condMutualInfo_eq_zero_iff hν X B C).1 h)
  set φ : κ → β → ℝ := fun c y => ∑ x, dist ν (pair C X) (c, x) * d x c y with hφ
  have hex : ∀ c, ∃ y, ∀ y', φ c y ≤ φ c y' := fun c => by
    obtain ⟨y, -, hy⟩ := (univ : Finset β).exists_min_image (φ c) univ_nonempty
    exact ⟨y, fun y' => hy y' (mem_univ _)⟩
  choose f hf using hex
  refine ⟨f, ?_⟩
  have e₁ : ∑ ω, ν ω * d (X ω) (C ω) (f (C ω)) = ∑ c, φ c (f c) := by
    have := sum_dist_mul ν (pair C X) fun t : κ × a => d t.2 t.1 (f t.1)
    rw [Fintype.sum_prod_type] at this
    exact this.symm
  have e₂ : ∑ ω, ν ω * d (X ω) (C ω) (g (C ω, B ω)) = ∑ c, ∑ b,
      dist ν (pair C B) (c, b) / dist ν C c * φ c (g (c, b)) := by
    have := sum_dist_mul ν (pair C (pair X B)) fun t : κ × a × σ => d t.2.1 t.1 (g (t.1, t.2.2))
    rw [hlaw] at this
    simp only [pair] at this
    rw [← this, Fintype.sum_prod_type]
    refine sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [hφ, mul_sum, condProdDist]
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun b _ => ?_
    ring
  rw [e₁, e₂]
  refine sum_le_sum fun c _ => ?_
  have hb : ∑ b, dist ν (pair C B) (c, b) = dist ν C c := by
    have := dist_fst (dist ν (pair C B)) c
    rw [← this, ← dist_comp_eq]
    rfl
  by_cases hc : dist ν C c = 0
  · have h0 : φ c (f c) = 0 := by
      simp only [hφ]
      refine sum_eq_zero fun x _ => ?_
      have hle := dist_pair_le_left hν C X c x
      have h₀ := (hν.dist (pair C X)).nonneg (c, x)
      rw [hc] at hle
      rw [le_antisymm hle h₀, zero_mul]
    rw [h0]
    simp [hc]
  · calc φ c (f c) = ∑ b, dist ν (pair C B) (c, b) / dist ν C c * φ c (f c) := by
          rw [← sum_mul, ← sum_div, hb, div_self hc, one_mul]
      _ ≤ _ := sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hf c _)
          (div_nonneg ((hν.dist _).nonneg _) ((hν.dist _).nonneg _))

/-- **The chain rule, in any order of the letters.** If the variable `F i` is a function of the
conditioning variable `C` and of the letters before `i`, then `H(Xⁿ | C) ≤ ∑ᵢ H(Xᵢ | F i)`. -/
theorem condEntropy_le_sum_of_order {γ : Type*} [Fintype γ] [Nonempty γ] [Nonempty Ω] {n : ℕ}
    (hν : IsPMF ν)
    (X : Ω → Fin n → γ) (C : Ω → κ) (ord : Fin n ≃ Fin n) {τ : Fin n → Type*}
    [∀ i, Fintype (τ i)] (F : ∀ i, Ω → τ i)
    (hF : ∀ i ω ω', C ω = C ω' → (∀ t, ord.symm t < ord.symm i → X ω t = X ω' t) →
      F i ω = F i ω') :
    H[X | C ; ν] ≤ ∑ i, H[fun ω => X ω i | F i ; ν] := by
  classical
  set Y : ℕ → Ω → γ := fun k ω => if h : k < n then X ω (ord ⟨k, h⟩) else Classical.arbitrary γ
    with hY
  have hc := chain_rule_entropy_cond hν Y C n
  have hpre : H[prefixRV Y n | C ; ν] = H[X | C ; ν] := by
    refine condEntropy_congr_left hν C (fun x (k : Fin n) => x (ord k)) (fun x x' h => ?_)
      fun ω => ?_
    · funext t
      have := congrFun h (ord.symm t)
      simpa using this
    · funext k
      simp [prefixRV, hY]
  rw [hpre, sum_range] at hc
  rw [hc, ← ord.sum_comp fun i => H[fun ω => X ω i | F i ; ν]]
  refine sum_le_sum fun k _ => ?_
  have hYk : Y k = fun ω => X ω (ord k) := by
    funext ω
    simp [hY]
  rw [hYk]
  have hne : Nonempty (τ (ord k)) := ⟨F _ (Classical.arbitrary Ω)⟩
  obtain ⟨G, hG⟩ : ∃ G : κ × (Fin k → γ) → τ (ord k), ∀ ω, F (ord k) ω =
    G (pair C (prefixRV Y k) ω) := by
    refine exists_factor fun ω ω' h => ?_
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    refine hF _ _ _ h₁ fun t ht => ?_
    have ht' : ((ord.symm t : Fin n) : ℕ) < k := by
      rw [ord.symm_apply_apply] at ht
      exact Fin.lt_def.1 ht
    have e : ∀ ω, prefixRV Y k ω ⟨_, ht'⟩ = X ω t := fun ω => by
      change (if h : ((ord.symm t : Fin n) : ℕ) < n then X ω (ord ⟨_, h⟩) else _) = X ω t
      rw [dite_eq_left (ord.symm t).isLt]
      simp
    have := congrFun h₂ ⟨_, ht'⟩
    rwa [e, e] at this
  have := condEntropy_le_condEntropy_comp hν (fun ω => X ω (ord k)) (pair C (prefixRV Y k)) G
  have e : G ∘ pair C (prefixRV Y k) = F (ord k) := by
    funext ω
    exact (hG ω).symm
  rwa [e] at this

end Tools

/-! ### The auxiliary letters -/

section Letters

universe u

variable {α₁ α₂ : Type u} {β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] {q : ℕ} {spk : Fin q → Bool}
  {M : Fin q → ℕ} [∀ l, NeZero (M l)] {n : ℕ} [NeZero n] [NeZero q] {P : α₁ × α₂ → ℝ}

/-- The alphabet of the auxiliary letters. -/
abbrev KUps (n : ℕ) (M : Fin q → ℕ) (α₁ α₂ : Type u) :=
  Fin n × (Fin n → Option α₁) × (Fin n → Option α₂) × Σ l, Fin (M l)

instance : Nonempty (KUps n M α₁ α₂) := ⟨(0, fun _ => none, fun _ => none, ⟨0, 0⟩)⟩

/-- The index of the round `l` in a tagged index. -/
def unTag (s : Σ l, Fin (M l)) (l : Fin q) : Fin (M l) :=
  if h : s.1 = l then h ▸ s.2 else 0

omit [NeZero q] in
lemma unTag_mk (l : Fin q) (m : Fin (M l)) : unTag ⟨l, m⟩ l = m := by
  simp [unTag]

/-- The side information `(X₁^{i-1}, X_{2,i+1}^n)` of the time `i`. -/
def kSide (i : Fin n) (ω : Fin n → α₁ × α₂) : (Fin n → Option α₁) × (Fin n → Option α₂) :=
  (maskLt i (fstSeq ω), maskGe (i + 1) (sndSeq ω))

namespace KaspiCode

variable (c : KaspiCode spk M n α₁ α₂ β₁ β₂)

/-- **Page 21-25 of [elgamal2010]: the auxiliary letter** of the round `l`, at the time `z.2`, in
all the rounds with the side information. -/
def kU (l : Fin q) (z : (Fin n → α₁ × α₂) × Fin n) : KUps n M α₁ α₂ :=
  (z.2, (kSide z.2 z.1).1, (kSide z.2 z.1).2, ⟨l, c.tr z.1 l⟩)

/-- All the auxiliary letters. -/
def kUs (z : (Fin n → α₁ × α₂) × Fin n) : Fin q → KUps n M α₁ α₂ := fun l => c.kU l z

omit [NeZero n] [NeZero q] [Fintype α₁] [Fintype α₂] in
lemma hist_of_lt (ω : Fin n → α₁ × α₂) {r : ℕ} {l : Fin q} (h : (l : ℕ) < r) :
    c.hist ω r l = c.tr ω l := by
  have h₁ := runTo_of_lt (c.step (fstSeq ω) (sndSeq ω)) h
  rw [c.tr_apply]
  exact h₁

/-- The past of the auxiliary letters is the side information and the past of the indices. -/
lemma truncU_kUs_iff {a : Type*} [Fintype a] {ν : (Fin n → α₁ × α₂) → ℝ} (hν : IsPMF ν)
    {b x : Type*} [Fintype b] [Fintype x] (X : (Fin n → α₁ × α₂) → b) (Y : (Fin n → α₁ × α₂) → x)
    (S : (Fin n → α₁ × α₂) → a) (i : Fin n) {l : ℕ} (hl : 0 < l) :
    I[X : Y | pair (fun ω => c.hist ω l) (pair S (kSide i)) ; ν] =
    I[X : Y | pair S (fun ω => truncU l (c.kUs (ω, i))) ; ν] := by
  classical
  have l₀ : (0 : ℕ) < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine condMutualInfo_congr_comp hν X Y
    (fun w => (w.2.1, fun l' => if (l' : ℕ) < l then
      (i, w.2.2.1, w.2.2.2, (⟨l', w.1 l'⟩ : Σ l, Fin (M l))) else Classical.arbitrary _))
    (fun w => ((fun l' => if (l' : ℕ) < l then unTag (w.2 l').2.2.2 l' else
      Classical.arbitrary _), w.1, (w.2 ⟨0, l₀⟩).2.1, (w.2 ⟨0, l₀⟩).2.2.1)) ?_ ?_
  · funext ω
    simp only [Function.comp, pair]
    refine Prod.ext rfl ?_
    funext l'
    simp only [truncU, kUs, kU]
    split_ifs with h
    · rw [c.hist_of_lt ω h]
    · rfl
  · funext ω
    simp only [Function.comp, pair]
    have hmask : truncU l (c.kUs (ω, i)) ⟨0, l₀⟩ = c.kU ⟨0, l₀⟩ (ω, i) := by
      simp [truncU, kUs, hl]
    refine Prod.ext ?_ (Prod.ext rfl (Prod.ext ?_ ?_))
    · funext l'
      simp only [truncU, kUs, kU]
      split_ifs with h
      · rw [c.hist_of_lt ω h, unTag_mk]
      · exact runTo_of_le _ (not_lt.1 h)
    · rw [hmask]
      rfl
    · rw [hmask]
      rfl

/-- **Claim (b) of page 21-25 of [elgamal2010], at one time and for a later round.** -/
lemma markov_letter_pos (hP : IsPMF P) {a b : Type*} [Fintype a] [Fintype b]
    (ξs : α₁ × α₂ → a) (ξo : α₁ × α₂ → b) (i : Fin n) (l : Fin q) (hl : 0 < (l : ℕ))
    (N : I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : fun ω => c.tr ω l |
      pair (fun ω => c.hist ω l) (pair (fun ω => ξs (ω i)) (kSide i)) ; iidPMF P n] = 0) :
    I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : fun ω => c.kU l (ω, i) |
      pair (fun ω => ξs (ω i)) (fun ω => truncU l (c.kUs (ω, i))) ; iidPMF P n] = 0 := by
  have hν := iidPMF_isPMF hP n
  rw [← c.truncU_kUs_iff hν _ _ _ i hl, ← N, condMutualInfo, condMutualInfo]
  congr 1
  refine condEntropy_eq_of_comp hν _
    (fun w => (unTag w.1.2.2.2 l, w.2)) (fun w => (((i, w.2.2.2.1, w.2.2.2.2,
      (⟨l, w.1⟩ : Σ l, Fin (M l))) : KUps n M α₁ α₂), w.2)) ?_ ?_
  · funext ω
    simp only [Function.comp, pair, kU, unTag_mk]
  · funext ω
    simp only [Function.comp, pair, kU]

/-- **Claim (b) of page 21-25 of [elgamal2010], with time sharing, for a later round.** -/
theorem markov_mix_pos (hP : IsPMF P) {a b : Type*} [Fintype a] [Fintype b]
    (ξs : α₁ × α₂ → a) (ξo : α₁ × α₂ → b) (l : Fin q) (hl : 0 < (l : ℕ))
    (N : ∀ i, I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : fun ω => c.tr ω l |
      pair (fun ω => c.hist ω l) (pair (fun ω => ξs (ω i)) (kSide i)) ; iidPMF P n] = 0) :
    I[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) : fun z => c.kU l z |
      pair (fun z => ξs (z.1 z.2)) (fun z => truncU l (c.kUs z)) ;
      mixLaw (iidPMF P n) (Fin n)] = 0 := by
  have l₀ : (0 : ℕ) < q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine condMutualInfo_mix_zero (iidPMF_isPMF hP n) _ _ _ (fun w => (w.2 ⟨0, l₀⟩).1)
    (fun z => ?_) fun i => c.markov_letter_pos hP ξs ξo i l hl (N i)
  simp [truncU, kUs, kU, hl]

/-- **Claim (b) of page 21-25 of [elgamal2010], with time sharing, for the first round.** The letter
of the sources at a uniform time is independent of the time. -/
theorem markov_mix_zero (hP : IsPMF P) {a b : Type*} [Fintype a] [Fintype b]
    (ξs : α₁ × α₂ → a) (ξo : α₁ × α₂ → b) (l : Fin q) (hl : (l : ℕ) = 0)
    (N : ∀ i, I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : fun ω => c.tr ω l |
      pair (fun ω => c.hist ω l) (pair (fun ω => ξs (ω i)) (kSide i)) ; iidPMF P n] = 0) :
    I[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) : fun z => c.kU l z |
      pair (fun z => ξs (z.1 z.2)) (fun z => truncU l (c.kUs z)) ;
      mixLaw (iidPMF P n) (Fin n)] = 0 := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hμ := iidPMF_isPMF hP n
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  -- the entropy without the auxiliary letter
  set ρ : a × b → ℝ := dist P (pair ξs ξo) with hρ
  have hlaw : ∀ i, dist (iidPMF P n) (fun ω : Fin n → α₁ × α₂ => (ξs (ω i), ξo (ω i))) = ρ := by
    intro i
    have h₁ := dist_comp_eq (iidPMF P n) (fun ω : Fin n → α₁ × α₂ => ω i) (pair ξs ξo)
    have h₂ : dist (iidPMF P n) (fun ω : Fin n → α₁ × α₂ => ω i) = P := by
      funext x
      exact dist_iidPMF_coord hP i x
    rw [h₂] at h₁
    exact h₁
  have hρp : IsPMF ρ := hP.dist _
  have hH₀ : ∀ i, H[fun ω : Fin n → α₁ × α₂ => ξo (ω i) | fun ω => ξs (ω i) ; iidPMF P n] =
      H[Prod.snd | Prod.fst ; ρ] := fun i =>
    condEntropy_eq_of_dist_pair_eq hμ hρp (by rw [dist_pair_fst_snd]; exact hlaw i)
  have hH₁ : H[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) | fun z => ξs (z.1 z.2) ;
      mixLaw (iidPMF P n) (Fin n)] = H[Prod.snd | Prod.fst ; ρ] := by
    refine condEntropy_eq_of_dist_pair_eq hν hρp ?_
    rw [dist_pair_fst_snd]
    funext t
    have e : pair (fun z : (Fin n → α₁ × α₂) × Fin n => ξs (z.1 z.2)) (fun z => ξo (z.1 z.2)) =
        fun z => (ξs (z.1 z.2), ξo (z.1 z.2)) := rfl
    rw [e, dist_mixLaw]
    simp only [hlaw, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  -- the letter of time `i`
  have hzero : ∀ i, I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : fun ω => c.kU l (ω, i) |
      fun ω => ξs (ω i) ; iidPMF P n] = 0 := by
    intro i
    have h₁ := chain_rule_condMutualInfo hμ (fun ω : Fin n → α₁ × α₂ => ξo (ω i))
      (fun ω => c.tr ω l) (kSide i) (fun ω => ξs (ω i))
    have h₂ : I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : kSide i | fun ω => ξs (ω i) ;
        iidPMF P n] = 0 := by
      have h₃ := chain_rule_mutualInfo₂ hμ (kSide i) (fun ω : Fin n → α₁ × α₂ => ξo (ω i))
        (fun ω => ξs (ω i))
      have h₄ : I[kSide i : pair (fun ω : Fin n → α₁ × α₂ => ξo (ω i)) (fun ω => ξs (ω i)) ;
          iidPMF P n] = 0 := by
        refine mutualInfo_iid_split hP (fun t => t ≠ i) (fun ω ω' h => ?_) fun ω ω' h => ?_
        · refine Prod.ext ?_ ?_ <;> funext t
          · by_cases ht : (t : ℕ) < i
            · have : t ≠ i := fun e => by
                rw [e] at ht
                exact lt_irrefl _ ht
              simp only [kSide, maskLt, ht, ite_true, fstSeq, h t this]
            · simp only [kSide, maskLt, ht, ite_false]
          · by_cases ht : (t : ℕ) < i + 1
            · simp only [kSide, maskGe, ht, ite_true]
            · have : t ≠ i := fun e => by
                rw [e] at ht
                omega
              simp only [kSide, maskGe, ht, ite_false, sndSeq, h t this]
        · have hi : ω i = ω' i := h i (by simp)
          simp only [pair, hi]
      have h₅ := mutualInfo_nonneg hμ (kSide i) (fun ω : Fin n → α₁ × α₂ => ξs (ω i))
      have h₆ := condMutualInfo_nonneg hμ (kSide i) (fun ω : Fin n → α₁ × α₂ => ξo (ω i))
        (fun ω => ξs (ω i))
      rw [condMutualInfo_comm hμ]
      linarith
    have h₃ : I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : fun ω => c.tr ω l |
        pair (kSide i) (fun ω => ξs (ω i)) ; iidPMF P n] = 0 := by
      rw [← N i]
      refine condMutualInfo_congr_comp hμ _ _
        (fun w : ((Fin n → Option α₁) × (Fin n → Option α₂)) × a =>
          ((fun l' : Fin q => Classical.arbitrary (Fin (M l'))), w.2, w.1))
        (fun w : (∀ l', Fin (M l')) × a × (Fin n → Option α₁) × (Fin n → Option α₂) =>
          (w.2.2, w.2.1)) ?_ rfl
      funext ω
      simp only [Function.comp, pair]
      refine Prod.ext ?_ rfl
      funext l'
      exact runTo_of_le _ (by rw [hl]; omega)
    rw [h₂, h₃, add_zero] at h₁
    have e : I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) : fun ω => c.kU l (ω, i) |
        fun ω => ξs (ω i) ; iidPMF P n] = I[fun ω : Fin n → α₁ × α₂ => ξo (ω i) :
        pair (fun ω => c.tr ω l) (kSide i) | fun ω => ξs (ω i) ; iidPMF P n] := by
      rw [condMutualInfo, condMutualInfo]
      congr 1
      refine condEntropy_eq_of_comp hμ _
        (fun w => ((unTag w.1.2.2.2 l, w.1.2.1, w.1.2.2.1), w.2))
        (fun w => (((i, w.1.2.1, w.1.2.2, (⟨l, w.1.1⟩ : Σ l, Fin (M l))) : KUps n M α₁ α₂), w.2))
        ?_ ?_
      · funext ω
        simp only [Function.comp, pair, kU, unTag_mk]
      · funext ω
        simp only [Function.comp, pair, kU]
    rw [e, h₁]
  -- the average
  have hmix : H[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) |
      pair (fun z => c.kU l z) (fun z => ξs (z.1 z.2)) ; mixLaw (iidPMF P n) (Fin n)] =
      H[Prod.snd | Prod.fst ; ρ] := by
    have h₁ := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α₁ × α₂) => ξo (ω i))
      (b := fun _ : Fin n => KUps n M α₁ α₂ × a) fun i ω => (c.kU l (ω, i), ξs (ω i))
    simp only [Fintype.card_fin] at h₁
    have h₂ : H[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) |
        pair (fun z => c.kU l z) (fun z => ξs (z.1 z.2)) ; mixLaw (iidPMF P n) (Fin n)] =
        H[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) |
          fun z => (⟨z.2, c.kU l (z.1, z.2), ξs (z.1 z.2)⟩ : Σ _ : Fin n, KUps n M α₁ α₂ × a) ;
          mixLaw (iidPMF P n) (Fin n)] :=
      condEntropy_eq_of_comp hν _ (fun w => ⟨w.1.1, w⟩) (fun s => s.2) (by
        funext z
        rfl) rfl
    rw [h₂, h₁]
    have h₃ : ∀ i, H[fun ω : Fin n → α₁ × α₂ => ξo (ω i) | fun ω => (c.kU l (ω, i), ξs (ω i)) ;
        iidPMF P n] = H[Prod.snd | Prod.fst ; ρ] := fun i => by
      have h₄ := hzero i
      rw [condMutualInfo, hH₀ i] at h₄
      have : H[fun ω : Fin n → α₁ × α₂ => ξo (ω i) | fun ω => (c.kU l (ω, i), ξs (ω i)) ;
          iidPMF P n] = H[fun ω : Fin n → α₁ × α₂ => ξo (ω i) |
          pair (fun ω => c.kU l (ω, i)) (fun ω => ξs (ω i)) ; iidPMF P n] := rfl
      rw [this]
      linarith
    simp only [h₃, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  have e₀ : I[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) : fun z => c.kU l z |
      pair (fun z => ξs (z.1 z.2)) (fun z => truncU l (c.kUs z)) ;
      mixLaw (iidPMF P n) (Fin n)] = I[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) :
      fun z => c.kU l z | fun z => ξs (z.1 z.2) ; mixLaw (iidPMF P n) (Fin n)] := by
    refine condMutualInfo_congr_comp hν _ _ (fun w : a × (Fin q → KUps n M α₁ α₂) => w.1)
      (fun w : a => (w, fun _ : Fin q => Classical.arbitrary (KUps n M α₁ α₂))) rfl ?_
    funext z
    simp only [Function.comp, pair]
    refine Prod.ext rfl ?_
    funext l'
    simp [truncU, hl]
  rw [e₀, condMutualInfo, hH₁, hmix, sub_self]

/-! ### The two forms of the past and of the mask at a time -/

omit [NeZero n] [NeZero q] in
/-- The information from Lemma 1, for a round of node 1, at the time `i`. -/
lemma normal₁ (hP : IsPMF P) (a₀ : α₁) (b₀ : α₂) (l : Fin q) (hs : spk l = true) (i : Fin n) :
    I[fun ω : Fin n → α₁ × α₂ => (ω i).2 : fun ω => c.tr ω l |
      pair (fun ω => c.hist ω l) (pair (fun ω => (ω i).1) (kSide i)) ; iidPMF P n] = 0 := by
  classical
  have hμ := iidPMF_isPMF hP n
  have h₀ := (c.condMutualInfo_speak hP a₀ b₀ (i + 1) l).1 hs
  set Z := pair (fun ω : Fin n → α₁ × α₂ => c.hist ω l)
    (pair (fun ω => maskLt (i + 1) (fstSeq ω)) (fun ω => maskGe (i + 1) (sndSeq ω))) with hZ
  have h₁ : I[fun ω : Fin n → α₁ × α₂ => (ω i).2 : fun ω => c.tr ω l | Z ; iidPMF P n] = 0 := by
    have hle := condMutualInfo_comp_le hμ (fun ω => c.tr ω l)
      (fun ω : Fin n → α₁ × α₂ => maskLt (i + 1) (sndSeq ω)) Z (fun m => (m i).getD b₀)
    have e : (fun m : Fin n → Option α₂ => (m i).getD b₀) ∘
        (fun ω : Fin n → α₁ × α₂ => maskLt (i + 1) (sndSeq ω)) = fun ω => (ω i).2 := by
      funext ω
      simp [maskLt, sndSeq]
    have h₀' : I[fun ω => c.tr ω l : fun ω : Fin n → α₁ × α₂ => maskLt (i + 1) (sndSeq ω) | Z ;
        iidPMF P n] = 0 := by
      rw [condMutualInfo_comm hμ]
      exact h₀
    rw [e, h₀'] at hle
    rw [condMutualInfo_comm hμ]
    exact le_antisymm hle (condMutualInfo_nonneg hμ _ _ _)
  rw [← h₁]
  refine (condMutualInfo_congr_comp hμ _ _
    (fun w : (∀ l', Fin (M l')) × (Fin n → Option α₁) × (Fin n → Option α₂) =>
      (w.1, (w.2.1 i).getD a₀, (fun j : Fin n => if (j : ℕ) < i then w.2.1 j else none), w.2.2))
    (fun w : (∀ l', Fin (M l')) × α₁ × (Fin n → Option α₁) × (Fin n → Option α₂) =>
      (w.1, Function.update w.2.2.1 i (some w.2.1), w.2.2.2)) ?_ ?_).symm
  · funext ω
    simp only [Function.comp, hZ, pair, kSide]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
    · simp [maskLt, fstSeq]
    · funext j
      simp only [maskLt]
      by_cases h : (j : ℕ) < i
      · have : (j : ℕ) < i + 1 := by omega
        simp [h, this]
      · simp [h]
  · funext ω
    simp only [Function.comp, hZ, pair, kSide]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext j
    by_cases hj : j = i
    · subst hj
      simp [maskLt, fstSeq]
    · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      simp only [Function.update_of_ne hj, maskLt]
      have : ((j : ℕ) < i + 1) ↔ ((j : ℕ) < i) := by omega
      simp [this]

omit [NeZero n] [NeZero q] in
/-- The information from Lemma 1, for a round of node 2, at the time `i`. -/
lemma normal₂ (hP : IsPMF P) (a₀ : α₁) (b₀ : α₂) (l : Fin q) (hs : spk l = false) (i : Fin n) :
    I[fun ω : Fin n → α₁ × α₂ => (ω i).1 : fun ω => c.tr ω l |
      pair (fun ω => c.hist ω l) (pair (fun ω => (ω i).2) (kSide i)) ; iidPMF P n] = 0 := by
  classical
  have hμ := iidPMF_isPMF hP n
  have h₀ := (c.condMutualInfo_speak hP a₀ b₀ i l).2 hs
  set Z := pair (fun ω : Fin n → α₁ × α₂ => c.hist ω l)
    (pair (fun ω => maskLt i (fstSeq ω)) (fun ω => maskGe i (sndSeq ω))) with hZ
  have h₁ : I[fun ω : Fin n → α₁ × α₂ => (ω i).1 : fun ω => c.tr ω l | Z ; iidPMF P n] = 0 := by
    have hle := condMutualInfo_comp_le hμ (fun ω => c.tr ω l)
      (fun ω : Fin n → α₁ × α₂ => maskGe i (fstSeq ω)) Z (fun m => (m i).getD a₀)
    have e : (fun m : Fin n → Option α₁ => (m i).getD a₀) ∘
        (fun ω : Fin n → α₁ × α₂ => maskGe i (fstSeq ω)) = fun ω => (ω i).1 := by
      funext ω
      simp [maskGe, fstSeq]
    have h₀' : I[fun ω => c.tr ω l : fun ω : Fin n → α₁ × α₂ => maskGe i (fstSeq ω) | Z ;
        iidPMF P n] = 0 := by
      rw [condMutualInfo_comm hμ]
      exact h₀
    rw [e, h₀'] at hle
    rw [condMutualInfo_comm hμ]
    exact le_antisymm hle (condMutualInfo_nonneg hμ _ _ _)
  rw [← h₁]
  refine (condMutualInfo_congr_comp hμ _ _
    (fun w : (∀ l', Fin (M l')) × (Fin n → Option α₁) × (Fin n → Option α₂) =>
      (w.1, (w.2.2 i).getD b₀, w.2.1, Function.update w.2.2 i none))
    (fun w : (∀ l', Fin (M l')) × α₂ × (Fin n → Option α₁) × (Fin n → Option α₂) =>
      (w.1, w.2.2.1, Function.update w.2.2.2 i (some w.2.1))) ?_ ?_).symm
  · funext ω
    simp only [Function.comp, hZ, pair, kSide]
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl ?_))
    · simp [maskGe, sndSeq]
    · funext j
      by_cases hj : j = i
      · subst hj
        simp [maskGe]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        simp only [Function.update_of_ne hj, maskGe]
        have : ((j : ℕ) < i + 1) ↔ ((j : ℕ) < i) := by omega
        simp [this]
  · funext ω
    simp only [Function.comp, hZ, pair, kSide]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    funext j
    by_cases hj : j = i
    · subst hj
      simp [maskGe, sndSeq]
    · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      simp only [Function.update_of_ne hj, maskGe]
      have : ((j : ℕ) < i + 1) ↔ ((j : ℕ) < i) := by omega
      simp [this]

/-- The Markov chains of the law of a code. -/
theorem markov_mix (hP : IsPMF P) (a₀ : α₁) (b₀ : α₂) (l : Fin q) :
    (spk l = true → I[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).2 : fun z => c.kU l z |
      pair (fun z => (z.1 z.2).1) (fun z => truncU l (c.kUs z)) ;
      mixLaw (iidPMF P n) (Fin n)] = 0) ∧
    (spk l = false → I[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).1 : fun z => c.kU l z |
      pair (fun z => (z.1 z.2).2) (fun z => truncU l (c.kUs z)) ;
      mixLaw (iidPMF P n) (Fin n)] = 0) := by
  constructor
  · intro hs
    by_cases hl : (l : ℕ) = 0
    · exact c.markov_mix_zero hP Prod.fst Prod.snd l hl fun i => c.normal₁ hP a₀ b₀ l hs i
    · exact c.markov_mix_pos hP Prod.fst Prod.snd l (Nat.pos_of_ne_zero hl)
        fun i => c.normal₁ hP a₀ b₀ l hs i
  · intro hs
    by_cases hl : (l : ℕ) = 0
    · exact c.markov_mix_zero hP Prod.snd Prod.fst l hl fun i => c.normal₂ hP a₀ b₀ l hs i
    · exact c.markov_mix_pos hP Prod.snd Prod.fst l (Nat.pos_of_ne_zero hl)
        fun i => c.normal₂ hP a₀ b₀ l hs i

/-! ### The rates -/

omit [NeZero n] [NeZero q] [Fintype α₁] [Fintype α₂] in
/-- The transcript from the indices of node 1 and the source of node 2. -/
lemma tr_eq_run_fst (ω : Fin n → α₁ × α₂) :
    c.tr ω = run fun l h => if _ : spk l = true then c.tr ω l else c.enc₂ l (sndSeq ω) h := by
  refine run_congr fun l => ?_
  by_cases hl : spk l = true
  · simp only [hl, ↓reduceDIte]
    exact (c.tr_apply ω l).symm
  · simp [step, hl]

omit [NeZero n] [NeZero q] [Fintype α₁] [Fintype α₂] in
/-- The transcript from the indices of node 2 and the source of node 1. -/
lemma tr_eq_run_snd (ω : Fin n → α₁ × α₂) :
    c.tr ω = run fun l h => if _ : spk l = false then c.tr ω l else c.enc₁ l (fstSeq ω) h := by
  refine run_congr fun l => ?_
  by_cases hl : spk l = false
  · simp only [hl, ↓reduceDIte]
    exact (c.tr_apply ω l).symm
  · have : spk l = true := by simpa using hl
    simp [step, this]

/-- `H(X | Y) ≤ log |𝒵| + H(X | Z, Y)`. -/
lemma _root_.InfoTheory.condEntropy_le_log_add {Ω a b z : Type*} [Fintype Ω] [Fintype a] [Fintype b]
    [Fintype z] {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → a) (Y : Ω → b) (Z : Ω → z) :
    H[X | Y ; μ] ≤ log (Fintype.card z) + H[X | pair Z Y ; μ] := by
  have hc1 := chain_rule_cond hμ X Z Y
  have hc2 := chain_rule_cond hμ Z X Y
  have hswap : H[pair X Z | Y ; μ] = H[pair Z X | Y ; μ] :=
    condEntropy_congr_left hμ Y Prod.swap Prod.swap_injective fun _ => rfl
  have h0 := condEntropy_nonneg hμ Z (pair X Y)
  have h1 := (condEntropy_le_entropy hμ Z Y).trans (entropyRV_le_log_card hμ Z)
  linarith

omit [∀ l, NeZero (M l)] [NeZero q] [NeZero n] in
lemma card_rounds (b : Bool) :
    Fintype.card (∀ l : {l // spk l = b}, Fin (M l)) = ∏ l with spk l = b, M l := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact (prod_subtype (univ.filter fun l => spk l = b) (by simp) M).symm

/-- The law at a uniform time of the two source letters. -/
lemma condEntropy_mix_letters (hP : IsPMF P) {a b : Type*} [Fintype a] [Fintype b]
    (ξs : α₁ × α₂ → a) (ξo : α₁ × α₂ → b) :
    H[fun z : (Fin n → α₁ × α₂) × Fin n => ξo (z.1 z.2) | fun z => ξs (z.1 z.2) ;
      mixLaw (iidPMF P n) (Fin n)] = H[ξo | ξs ; P] := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hμ := iidPMF_isPMF hP n
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  refine condEntropy_eq_of_dist_pair_eq hν hP ?_
  have e := dist_comp_eq (mixLaw (iidPMF P n) (Fin n)) (fun z : (Fin n → α₁ × α₂) × Fin n => z.1
    z.2)
    (pair ξs ξo)
  rw [dist_mix_coord hP hn0] at e
  exact e

/-- **Page 21-28 of [elgamal2010]: the rate of node 1.** -/
theorem rate₁ (hP : IsPMF P) :
    (n : ℝ) * I[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).1 : fun z => c.kUs z |
      fun z => (z.1 z.2).2 ; mixLaw (iidPMF P n) (Fin n)] ≤
      log ((∏ l with spk l = true, M l : ℕ) : ℝ) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hμ := iidPMF_isPMF hP n
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  have hneΩ : Nonempty (Fin n → α₁ × α₂) := by
    obtain ⟨z⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
    exact ⟨fun _ => z⟩
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty α₁ := ⟨z₀.1⟩
  have hL := condEntropy_mix_letters (n := n) hP (Prod.snd : α₁ × α₂ → α₂) (Prod.fst : α₁ × α₂ → α₁)
  have hmix : H[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).1 |
      pair (fun z => c.kUs z) (fun z => (z.1 z.2).2) ; mixLaw (iidPMF P n) (Fin n)] =
      (n : ℝ)⁻¹ * ∑ i, H[fun ω : Fin n → α₁ × α₂ => (ω i).1 |
        fun ω => (c.kUs (ω, i), (ω i).2) ; iidPMF P n] := by
    have h₁ := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α₁ × α₂) => (ω i).1)
      (b := fun _ : Fin n => (Fin q → KUps n M α₁ α₂) × α₂) fun i ω => (c.kUs (ω, i), (ω i).2)
    simp only [Fintype.card_fin] at h₁
    rw [← h₁]
    exact condEntropy_eq_of_comp hν _ (fun w => ⟨(w.1 ⟨0, hq0⟩).1, w⟩) (fun s => s.2) (by
      funext z
      rfl) rfl
  have hsum : H[fstSeq | pair sndSeq c.tr ; iidPMF P n] ≤ ∑ i, H[fun ω : Fin n → α₁ × α₂ => (ω i).1
    |
      fun ω => (c.kUs (ω, i), (ω i).2) ; iidPMF P n] := by
    refine condEntropy_le_sum_of_order hμ fstSeq (pair sndSeq c.tr) (Equiv.refl _)
      (fun i ω => (c.kUs (ω, i), (ω i).2)) fun i ω ω' hC hX => ?_
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hC
    have hx : ∀ t, (ω' t).2 = (ω t).2 := fun t => (congrFun h₁ t).symm
    refine Prod.ext ?_ (hx i).symm
    funext l
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext t
      simp only [kUs, kU, kSide, maskLt]
      split_ifs with ht
      · exact congrArg some (hX t ht)
      · rfl
    · funext t
      simp only [kUs, kU, kSide, maskGe]
      split_ifs with ht
      · rfl
      · exact congrArg some (congrFun h₁ t)
    · simp only [kUs, kU]
      rw [show c.tr ω = c.tr ω' from h₂]
  have hfano := condEntropy_le_log_add hμ (fstSeq : (Fin n → α₁ × α₂) → Fin n → α₁) sndSeq
    (fun ω (l : {l // spk l = true}) => c.tr ω l)
  rw [card_rounds] at hfano
  have heq : H[fstSeq | pair (fun ω (l : {l // spk l = true}) => c.tr ω l) sndSeq ; iidPMF P n] =
      H[fstSeq | pair sndSeq c.tr ; iidPMF P n] := by
    refine condEntropy_eq_of_comp hμ _
      (fun w => (w.2, run fun l h => if hl : spk l = true then w.1 ⟨l, hl⟩ else c.enc₂ l w.2 h))
      (fun w => ((fun l => w.2 l), w.1)) ?_ rfl
    funext ω
    simp only [Function.comp, pair]
    refine Prod.ext rfl ?_
    exact c.tr_eq_run_fst ω
  have hiid := condEntropy_iid_fst hP n
  rw [condMutualInfo, hL, hmix, mul_sub, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
  have e : H[fstSeq | sndSeq ; iidPMF P n] = n * H[Prod.fst | Prod.snd ; P] := hiid
  linarith

/-- **Page 21-28 of [elgamal2010]: the rate of node 2.** -/
theorem rate₂ (hP : IsPMF P) :
    (n : ℝ) * I[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).2 : fun z => c.kUs z |
      fun z => (z.1 z.2).1 ; mixLaw (iidPMF P n) (Fin n)] ≤
      log ((∏ l with spk l = false, M l : ℕ) : ℝ) := by
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hμ := iidPMF_isPMF hP n
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  have hneΩ : Nonempty (Fin n → α₁ × α₂) := by
    obtain ⟨z⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
    exact ⟨fun _ => z⟩
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty α₂ := ⟨z₀.2⟩
  have hL := condEntropy_mix_letters (n := n) hP (Prod.fst : α₁ × α₂ → α₁) (Prod.snd : α₁ × α₂ → α₂)
  have hmix : H[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).2 |
      pair (fun z => c.kUs z) (fun z => (z.1 z.2).1) ; mixLaw (iidPMF P n) (Fin n)] =
      (n : ℝ)⁻¹ * ∑ i, H[fun ω : Fin n → α₁ × α₂ => (ω i).2 |
        fun ω => (c.kUs (ω, i), (ω i).1) ; iidPMF P n] := by
    have h₁ := condEntropy_mix hμ (fun (i : Fin n) (ω : Fin n → α₁ × α₂) => (ω i).2)
      (b := fun _ : Fin n => (Fin q → KUps n M α₁ α₂) × α₁) fun i ω => (c.kUs (ω, i), (ω i).1)
    simp only [Fintype.card_fin] at h₁
    rw [← h₁]
    exact condEntropy_eq_of_comp hν _ (fun w => ⟨(w.1 ⟨0, hq0⟩).1, w⟩) (fun s => s.2) (by
      funext z
      rfl) rfl
  have hsum : H[sndSeq | pair fstSeq c.tr ; iidPMF P n] ≤ ∑ i, H[fun ω : Fin n → α₁ × α₂ => (ω i).2
    |
      fun ω => (c.kUs (ω, i), (ω i).1) ; iidPMF P n] := by
    refine condEntropy_le_sum_of_order hμ sndSeq (pair fstSeq c.tr) Fin.revPerm
      (fun i ω => (c.kUs (ω, i), (ω i).1)) fun i ω ω' hC hX => ?_
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hC
    have hx : ∀ t, (ω' t).1 = (ω t).1 := fun t => (congrFun h₁ t).symm
    refine Prod.ext ?_ (hx i).symm
    funext l
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · funext t
      simp only [kUs, kU, kSide, maskLt]
      split_ifs with ht
      · exact congrArg some (congrFun h₁ t)
      · rfl
    · funext t
      simp only [kUs, kU, kSide, maskGe]
      split_ifs with ht
      · rfl
      · refine congrArg some (hX t ?_)
        simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.lt_def, Fin.val_rev]
        have := t.isLt
        have := i.isLt
        omega
    · simp only [kUs, kU]
      rw [show c.tr ω = c.tr ω' from h₂]
  have hfano := condEntropy_le_log_add hμ (sndSeq : (Fin n → α₁ × α₂) → Fin n → α₂) fstSeq
    (fun ω (l : {l // spk l = false}) => c.tr ω l)
  rw [card_rounds] at hfano
  have heq : H[sndSeq | pair (fun ω (l : {l // spk l = false}) => c.tr ω l) fstSeq ; iidPMF P n] =
      H[sndSeq | pair fstSeq c.tr ; iidPMF P n] := by
    refine condEntropy_eq_of_comp hμ _
      (fun w => (w.2, run fun l h => if hl : spk l = false then w.1 ⟨l, hl⟩ else c.enc₁ l w.2 h))
      (fun w => ((fun l => w.2 l), w.1)) ?_ rfl
    funext ω
    simp only [Function.comp, pair]
    refine Prod.ext rfl ?_
    exact c.tr_eq_run_snd ω
  have hiid := condEntropy_iid_snd hP n
  rw [condMutualInfo, hL, hmix, mul_sub, ← mul_assoc, mul_inv_cancel₀ hn'.ne', one_mul]
  have e : H[sndSeq | fstSeq ; iidPMF P n] = n * H[Prod.snd | Prod.fst ; P] := hiid
  linarith

/-! ### The distortions -/

/-- **Claim (a) of page 21-25 of [elgamal2010], at the distortion of `X₁`.** -/
lemma markov_dist₁ (hP : IsPMF P) (a₀ : α₁) (b₀ : α₂) :
    I[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).1 : fun z => maskLt z.2 (sndSeq z.1) |
      pair (fun z => c.kUs z) (fun z => (z.1 z.2).2) ; mixLaw (iidPMF P n) (Fin n)] = 0 := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hμ := iidPMF_isPMF hP n
  refine condMutualInfo_mix_zero hμ _ _ _ (fun w => (w.1 ⟨0, hq0⟩).1) (fun z => rfl) fun i => ?_
  have h₀ := c.condMutualInfo_trans hP a₀ b₀ i
  set Z := pair c.tr (pair (fun ω : Fin n → α₁ × α₂ => maskLt i (fstSeq ω))
    (fun ω => maskGe i (sndSeq ω))) with hZ
  have h₁ : I[fun ω : Fin n → α₁ × α₂ => (ω i).1 : fun ω => maskLt i (sndSeq ω) | Z ;
      iidPMF P n] = 0 := by
    have hle := condMutualInfo_comp_le hμ (fun ω : Fin n → α₁ × α₂ => maskLt i (sndSeq ω))
      (fun ω => maskGe i (fstSeq ω)) Z (fun m => (m i).getD a₀)
    have e : (fun m : Fin n → Option α₁ => (m i).getD a₀) ∘
        (fun ω : Fin n → α₁ × α₂ => maskGe i (fstSeq ω)) = fun ω => (ω i).1 := by
      funext ω
      simp [maskGe, fstSeq]
    have h₀' : I[fun ω : Fin n → α₁ × α₂ => maskLt i (sndSeq ω) : fun ω => maskGe i (fstSeq ω) |
        Z ; iidPMF P n] = 0 := by
      rw [condMutualInfo_comm hμ]
      exact h₀
    rw [e, h₀'] at hle
    rw [condMutualInfo_comm hμ]
    exact le_antisymm hle (condMutualInfo_nonneg hμ _ _ _)
  rw [← h₁]
  refine (condMutualInfo_congr_comp hμ _ _
    (fun w : (∀ l', Fin (M l')) × (Fin n → Option α₁) × (Fin n → Option α₂) =>
      ((fun l => ((i, w.2.1, Function.update w.2.2 i none, (⟨l, w.1 l⟩ : Σ l, Fin (M l))) :
        KUps n M α₁ α₂)), (w.2.2 i).getD b₀))
    (fun w : (Fin q → KUps n M α₁ α₂) × α₂ =>
      ((fun l => unTag (w.1 l).2.2.2 l), (w.1 ⟨0, hq0⟩).2.1,
        Function.update (w.1 ⟨0, hq0⟩).2.2.1 i (some w.2))) ?_ ?_).symm
  · funext ω
    simp only [Function.comp, hZ, pair]
    refine Prod.ext ?_ ?_
    · funext l
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl))
      funext j
      by_cases hj : j = i
      · subst hj
        simp [kUs, kU, kSide, maskGe]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        simp only [Function.update_of_ne hj, kUs, kU, kSide, maskGe]
        have : ((j : ℕ) < i + 1) ↔ ((j : ℕ) < i) := by omega
        simp [this]
    · simp [maskGe, sndSeq]
  · funext ω
    simp only [Function.comp, hZ, pair]
    refine Prod.ext ?_ (Prod.ext rfl ?_)
    · funext l
      simp [kUs, kU, unTag_mk]
    · funext j
      by_cases hj : j = i
      · subst hj
        simp [maskGe, sndSeq]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        simp only [Function.update_of_ne hj, kUs, kU, kSide, maskGe]
        have : ((j : ℕ) < i + 1) ↔ ((j : ℕ) < i) := by omega
        simp [this]

/-- **Claim (a) of page 21-25 of [elgamal2010], at the distortion of `X₂`.** -/
lemma markov_dist₂ (hP : IsPMF P) (a₀ : α₁) (b₀ : α₂) :
    I[fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).2 : fun z => maskGe (z.2 + 1) (fstSeq z.1) |
      pair (fun z => c.kUs z) (fun z => (z.1 z.2).1) ; mixLaw (iidPMF P n) (Fin n)] = 0 := by
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hμ := iidPMF_isPMF hP n
  refine condMutualInfo_mix_zero hμ _ _ _ (fun w => (w.1 ⟨0, hq0⟩).1) (fun z => rfl) fun i => ?_
  have h₀ := c.condMutualInfo_trans hP a₀ b₀ (i + 1)
  set Z := pair c.tr (pair (fun ω : Fin n → α₁ × α₂ => maskLt (i + 1) (fstSeq ω))
    (fun ω => maskGe (i + 1) (sndSeq ω))) with hZ
  have h₁ : I[fun ω : Fin n → α₁ × α₂ => (ω i).2 : fun ω => maskGe (i + 1) (fstSeq ω) | Z ;
      iidPMF P n] = 0 := by
    have hle := condMutualInfo_comp_le hμ (fun ω : Fin n → α₁ × α₂ => maskGe (i + 1) (fstSeq ω))
      (fun ω => maskLt (i + 1) (sndSeq ω)) Z (fun m => (m i).getD b₀)
    have e : (fun m : Fin n → Option α₂ => (m i).getD b₀) ∘
        (fun ω : Fin n → α₁ × α₂ => maskLt (i + 1) (sndSeq ω)) = fun ω => (ω i).2 := by
      funext ω
      simp [maskLt, sndSeq]
    rw [e, h₀] at hle
    rw [condMutualInfo_comm hμ]
    exact le_antisymm hle (condMutualInfo_nonneg hμ _ _ _)
  rw [← h₁]
  refine (condMutualInfo_congr_comp hμ _ _
    (fun w : (∀ l', Fin (M l')) × (Fin n → Option α₁) × (Fin n → Option α₂) =>
      ((fun l => ((i, Function.update w.2.1 i none, w.2.2, (⟨l, w.1 l⟩ : Σ l, Fin (M l))) :
        KUps n M α₁ α₂)), (w.2.1 i).getD a₀))
    (fun w : (Fin q → KUps n M α₁ α₂) × α₁ =>
      ((fun l => unTag (w.1 l).2.2.2 l), Function.update (w.1 ⟨0, hq0⟩).2.1 i (some w.2),
        (w.1 ⟨0, hq0⟩).2.2.1)) ?_ ?_).symm
  · funext ω
    simp only [Function.comp, hZ, pair]
    refine Prod.ext ?_ ?_
    · funext l
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      funext j
      by_cases hj : j = i
      · subst hj
        simp [kUs, kU, kSide, maskLt]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        simp only [Function.update_of_ne hj, kUs, kU, kSide, maskLt]
        have : ((j : ℕ) < i + 1) ↔ ((j : ℕ) < i) := by omega
        simp [this]
    · simp [maskLt, fstSeq]
  · funext ω
    simp only [Function.comp, hZ, pair]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · funext l
      simp [kUs, kU, unTag_mk]
    · funext j
      by_cases hj : j = i
      · subst hj
        simp [maskLt, fstSeq]
      · have hne : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
        simp only [Function.update_of_ne hj, kUs, kU, kSide, maskLt]
        have : ((j : ℕ) < i + 1) ↔ ((j : ℕ) < i) := by omega
        simp [this]

/-- **The converse of Theorem 4 of Lecture 21 of [elgamal2010], for one code.** -/
theorem exists_kaspi_law [Finite β₁] [Finite β₂] [Nonempty β₁] [Nonempty β₂] (hP : IsPMF P)
    (d₁ : α₁ × α₂ → β₁ → ℝ) (d₂ : α₁ × α₂ → β₂ → ℝ) :
    ∃ (μ : α₁ × α₂ × (Fin q → KUps n M α₁ α₂) → ℝ) (f₁ : (Fin q → KUps n M α₁ α₂) → α₂ → β₁)
      (f₂ : (Fin q → KUps n M α₁ α₂) → α₁ → β₂), IsKaspiLaw P spk μ ∧
      (n : ℝ) * I[fun z : α₁ × α₂ × (Fin q → KUps n M α₁ α₂) => z.1 : fun z => z.2.2 |
        fun z => z.2.1 ; μ] ≤ log ((∏ l with spk l = true, M l : ℕ) : ℝ) ∧
      (n : ℝ) * I[fun z : α₁ × α₂ × (Fin q → KUps n M α₁ α₂) => z.2.1 : fun z => z.2.2 |
        fun z => z.1 ; μ] ≤ log ((∏ l with spk l = false, M l : ℕ) : ℝ) ∧
      ∑ z, μ z * d₁ (z.1, z.2.1) (f₁ z.2.2 z.2.1) ≤ c.distortion₁ P d₁ ∧
      ∑ z, μ z * d₂ (z.1, z.2.1) (f₂ z.2.2 z.1) ≤ c.distortion₂ P d₂ := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  classical
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨z₀⟩ : Nonempty (α₁ × α₂) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hμ := iidPMF_isPMF hP n
  have hν : IsPMF (mixLaw (iidPMF P n) (Fin n)) := mixLaw_isPMF hμ
  set ν := mixLaw (iidPMF P n) (Fin n) with hνd
  set W : (Fin n → α₁ × α₂) × Fin n → α₁ × α₂ × (Fin q → KUps n M α₁ α₂) :=
    fun z => ((z.1 z.2).1, (z.1 z.2).2, c.kUs z) with hW
  set l₀ : Fin q := ⟨0, hq0⟩
  -- the estimates
  let g₁ : ((Fin q → KUps n M α₁ α₂) × α₂) × (Fin n → Option α₂) → β₁ := fun w =>
    c.dec₁ (unmask z₀.2 (Function.update w.2 (w.1.1 l₀).1 (some w.1.2)) (w.1.1 l₀).2.2.1)
      (fun l => unTag (w.1.1 l).2.2.2 l) (w.1.1 l₀).1
  let g₂ : ((Fin q → KUps n M α₁ α₂) × α₁) × (Fin n → Option α₁) → β₂ := fun w =>
    c.dec₂ (unmask z₀.1 (Function.update (w.1.1 l₀).2.1 (w.1.1 l₀).1 (some w.1.2)) w.2)
      (fun l => unTag (w.1.1 l).2.2.2 l) (w.1.1 l₀).1
  obtain ⟨f₁, hf₁⟩ := exists_estimator_le hν (fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).1)
    (pair (fun z => c.kUs z) (fun z => (z.1 z.2).2)) (fun z => maskLt z.2 (sndSeq z.1)) g₁
    (fun x t y => d₁ (x, t.2) y)
    (c.markov_dist₁ hP z₀.1 z₀.2)
  obtain ⟨f₂, hf₂⟩ := exists_estimator_le hν (fun z : (Fin n → α₁ × α₂) × Fin n => (z.1 z.2).2)
    (pair (fun z => c.kUs z) (fun z => (z.1 z.2).1)) (fun z => maskGe (z.2 + 1) (fstSeq z.1)) g₂
    (fun x t y => d₂ (t.2, x) y)
    (c.markov_dist₂ hP z₀.1 z₀.2)
  have hg₁ : ∀ z : (Fin n → α₁ × α₂) × Fin n, g₁ (pair (fun z => c.kUs z)
      (fun z => (z.1 z.2).2) z, maskLt z.2 (sndSeq z.1)) =
      c.dec₁ (sndSeq z.1) (c.tr z.1) z.2 := fun z => by
    simp only [g₁, pair]
    have e₁ : (fun l => unTag (c.kUs z l).2.2.2 l) = c.tr z.1 := by
      funext l
      simp [kUs, kU, unTag_mk]
    have e₂ : unmask z₀.2 (Function.update (maskLt z.2 (sndSeq z.1)) (c.kUs z l₀).1
        (some (z.1 z.2).2)) (c.kUs z l₀).2.2.1 = sndSeq z.1 := by
      funext j
      have hi : (c.kUs z l₀).1 = z.2 := rfl
      rw [hi]
      by_cases hj : j = z.2
      · subst hj
        simp [unmask, sndSeq]
      · have hne : (j : ℕ) ≠ z.2 := fun h => hj (Fin.ext h)
        simp only [unmask, Function.update_of_ne hj, kUs, kU, kSide, maskLt, maskGe]
        by_cases hlt : (j : ℕ) < z.2
        · simp [hlt]
        · have : ¬ (j : ℕ) < z.2 + 1 := by omega
          simp [hlt, this]
    rw [e₁, e₂]
    rfl
  have hg₂ : ∀ z : (Fin n → α₁ × α₂) × Fin n, g₂ (pair (fun z => c.kUs z)
      (fun z => (z.1 z.2).1) z, maskGe (z.2 + 1) (fstSeq z.1)) =
      c.dec₂ (fstSeq z.1) (c.tr z.1) z.2 := fun z => by
    simp only [g₂, pair]
    have e₁ : (fun l => unTag (c.kUs z l).2.2.2 l) = c.tr z.1 := by
      funext l
      simp [kUs, kU, unTag_mk]
    have e₂ : unmask z₀.1 (Function.update (c.kUs z l₀).2.1 (c.kUs z l₀).1
        (some (z.1 z.2).1)) (maskGe (z.2 + 1) (fstSeq z.1)) = fstSeq z.1 := by
      funext j
      have hi : (c.kUs z l₀).1 = z.2 := rfl
      rw [hi]
      by_cases hj : j = z.2
      · subst hj
        simp [unmask, fstSeq]
      · have hne : (j : ℕ) ≠ z.2 := fun h => hj (Fin.ext h)
        simp only [unmask, Function.update_of_ne hj, kUs, kU, kSide, maskLt, maskGe]
        by_cases hlt : (j : ℕ) < z.2
        · have : (j : ℕ) < z.2 + 1 := by omega
          simp [hlt, this]
        · have : ¬ (j : ℕ) < z.2 + 1 := by omega
          simp [hlt, this]
    rw [e₁, e₂]
    rfl
  have hM := c.markov_mix hP z₀.1 z₀.2
  refine ⟨dist ν W, fun u x => f₁ (u, x), fun u x => f₂ (u, x), ⟨hν.dist W, ?_, fun l hs => ?_,
    fun l hs => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [← dist_comp_eq]
    exact dist_mix_coord hP hn0
  · have h₁ := (hM l).1 hs
    rw [condMutualInfo, condEntropy_dist hν W, condEntropy_dist hν W]
    rw [condMutualInfo] at h₁
    exact h₁
  · have h₁ := (hM l).2 hs
    rw [condMutualInfo, condEntropy_dist hν W, condEntropy_dist hν W]
    rw [condMutualInfo] at h₁
    exact h₁
  · rw [condMutualInfo, condEntropy_dist hν W, condEntropy_dist hν W]
    have h₁ := c.rate₁ hP
    rw [condMutualInfo] at h₁
    exact h₁
  · rw [condMutualInfo, condEntropy_dist hν W, condEntropy_dist hν W]
    have h₁ := c.rate₂ hP
    rw [condMutualInfo] at h₁
    exact h₁
  · rw [sum_dist_mul ν W fun z => d₁ (z.1, z.2.1) (f₁ (z.2.2, z.2.1))]
    refine hf₁.trans (le_of_eq ?_)
    simp only [hg₁]
    exact sum_mix_mul hn0 fun ω i => d₁ (ω i) (c.dec₁ (sndSeq ω) (c.tr ω) i)
  · rw [sum_dist_mul ν W fun z => d₂ (z.1, z.2.1) (f₂ (z.2.2, z.1))]
    refine hf₂.trans (le_of_eq ?_)
    simp only [hg₂]
    exact sum_mix_mul hn0 fun ω i => d₂ (ω i) (c.dec₂ (fstSeq ω) (c.tr ω) i)

end KaspiCode

end Letters

/-! ### The converse -/

section Converse

universe u

variable {α₁ α₂ : Type u} {β₁ β₂ : Type*} [Fintype α₁] [Fintype α₂] [Fintype β₁] [Fintype β₂]
  [Nonempty β₁] [Nonempty β₂] {q : ℕ} {spk : Fin q → Bool} {P : α₁ × α₂ → ℝ} {d₁ : α₁ × α₂ → β₁ → ℝ}
  {d₂ : α₁ × α₂ → β₂ → ℝ}

omit [Fintype β₁] [Fintype β₂] in
/-- **Theorem 4 of Lecture 21 of [elgamal2010], page 21-22: the converse.** A rate pair of the
`q`-round rate–distortion region satisfies the bounds up to `ε`. The notes bound the alphabets of
the auxiliary letters; we do not prove this bound. -/
theorem exists_kaspiInner_of_mem_kaspiRegion [Finite β₁] [Finite β₂] (hq : 0 < q) (hP : IsPMF P)
    {D₁ D₂ : ℝ} {R : ℝ × ℝ} (h : R ∈ kaspiRegion P spk d₁ d₂ D₁ D₂) {ε : ℝ} (hε : 0 < ε) :
    (R.1 + ε, R.2 + ε) ∈ kaspiInner P spk d₁ d₂ (D₁ + ε) (D₂ + ε) := by
  have := Fintype.ofFinite β₁
  have := Fintype.ofFinite β₂
  have hl2 := log_pos one_lt_two
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 h ε hε
  obtain ⟨hb₁, hb₂, hc⟩ := hb
  obtain ⟨n, ⟨M, hM, c, hs₁, hs₂, hd₁, hd₂⟩, hn⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hneq : NeZero q := ⟨hq.ne'⟩
  have hnen : NeZero n := ⟨hn.ne'⟩
  obtain ⟨μ, f₁, f₂, hμ, a₁, a₂, a₃, a₄⟩ := c.exists_kaspi_law hP d₁ d₂
  have hclose : b.1 ≤ R.1 + ε ∧ b.2 ≤ R.2 + ε := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt] at hdist
    constructor <;> linarith [hdist.1.1, hdist.2.1]
  have hsize : ∀ {b' R' : ℝ} (s : ℕ), 0 ≤ b' → b' ≤ R' → 0 < s → s ≤ 2 ^ ⌊(n : ℝ) * b'⌋₊ →
      log (s : ℝ) ≤ n * (R' * log 2) := fun {b' R'} s hb₀ hb' hs hle => by
    have hs' : (0 : ℝ) < s := by exact_mod_cast hs
    have h₁ : log (s : ℝ) ≤ log ((2 ^ ⌊(n : ℝ) * b'⌋₊ : ℕ) : ℝ) :=
      log_le_log hs' (by exact_mod_cast hle)
    refine h₁.trans ((log_two_pow_floor_le n hb₀).trans ?_)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb' hl2.le) hn'.le
  have hpos : ∀ b : Bool, 0 < ∏ l with spk l = b, M l := fun b =>
    prod_pos fun l _ => Nat.pos_of_ne_zero (NeZero.ne _)
  refine ⟨_, inferInstance, inferInstance, μ, f₁, f₂, hμ, ?_, ?_, a₃.trans hd₁, a₄.trans hd₂⟩
  · refine le_of_mul_le_mul_left (a₁.trans (hsize _ hb₁ hclose.1 (hpos true) hs₁)) hn'
  · refine le_of_mul_le_mul_left (a₂.trans (hsize _ hb₂ hclose.2 (hpos false) hs₂)) hn'

end Converse

end InfoTheory
