/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.PolyFiniteField
public import InfoTheoryLib.Network.NoiselessRouting

/-!
# Linear network codes

Linear network codes on an acyclic multigraph with edges of the same capacity, and the algebraic
approach of Koetter and Médard: the determinant of the transformation from the messages to what a
destination decodes is a polynomial in the coefficients of the code, and it is nonzero if and only
if the cut conditions hold.

## Main definitions

* `Multigraph V E`: an acyclic multigraph with edges `E`.
* `LinCoeff K E b V`: the coefficients of a linear code over `K`.
* `globalVec`: the coefficients of the messages in the symbol on an edge.
* `transfer`: the matrix `A_j(α)` of page 16-18.
* `LinVar`, `genericCoeff`, `detGeneric`: the polynomial `|A_j(x)|` of page 16-20.
* `LinCoeff.code`: the code of the coefficients.

## Main statements

* `exists_coeff_of_bit`: routing is a linear code with coefficients in `𝔽₂` and `A_j(α) = I`.
* `detGeneric_ne_zero_of_cuts`: the cut conditions imply `|A_j(x)| ≠ 0`.
* `exists_coeff_of_card_gt`: over a large enough field, coefficients with nonzero determinants for
  all destinations.
* `LinCoeff.code_correct`: a linear code with invertible matrices has no errors.
* `cuts_of_detGeneric_ne_zero`: `|A_j(x)| ≠ 0` implies the cut conditions.
* `card_not_invertible_le`: a random linear code works with high probability.
* `degreeOf_detGeneric_le`, `exists_coeff_of_card_gt`: a field with more than `|D| R` elements is
  enough, as stated on page 16-22.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
* R. Koetter and M. Médard, *An algebraic approach to network coding*, 2003
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Multigraphs and coefficients -/

/-- **Lecture 16 of [elgamal2010], page 16-16.** An acyclic multigraph, with nodes ordered so that
edges go up. Each edge carries one symbol. -/
structure Multigraph (V E : Type*) [LT V] where
  /-- The node an edge leaves. -/
  tail : E → V
  /-- The node an edge enters. -/
  head : E → V
  /-- Edges go up. -/
  lt : ∀ e, tail e < head e

/-- **Page 16-17 of [elgamal2010].** The coefficients of a linear code for messages of `b j` symbols
at node `j`: `y r e` multiplies the message symbol `r` on an edge out of its node, `x e' e`
multiplies the symbol of `e'` on an edge `e` out of the head of `e'`, and `z t e r` is the
coefficient of the symbol of `e` in the estimate of the symbol `r` at node `t`. -/
structure LinCoeff (K E : Type*) {V : Type*} (b : V → ℕ) where
  /-- The coefficients of the source encoders. -/
  y : (Σ j, Fin (b j)) → E → K
  /-- The coefficients of the relay encoders. -/
  x : E → E → K
  /-- The coefficients of the decoders. -/
  z : V → E → (Σ j, Fin (b j)) → K

variable {V E K L : Type*}

/-- **Page 16-18 of [elgamal2010].** The global coding vector: the coefficient of the message symbol
`r` in the symbol sent on the edge `e`. -/
def globalVec [LinearOrder V] [Fintype V] [Fintype E] [CommRing K] {b : V → ℕ}
    (G : Multigraph V E) (a : LinCoeff K E b) (e : E) (r : Σ j, Fin (b j)) : K :=
  (if r.1 = G.tail e then a.y r e else 0) +
    ∑ e' : {e' // G.head e' = G.tail e}, a.x e'.1 e * globalVec G a e'.1 r
termination_by (wellFounded_lt (α := V)).wrap (G.tail e)
decreasing_by
  exact (G.lt e'.1).trans_eq e'.2

variable [LinearOrder V] [Fintype V] [Fintype E] {b : V → ℕ}

section Vec

variable [CommRing K] [CommRing L]

lemma globalVec_eq (G : Multigraph V E) (a : LinCoeff K E b) (e : E) (r : Σ j, Fin (b j)) :
    globalVec G a e r = (if r.1 = G.tail e then a.y r e else 0) +
      ∑ e' : {e' // G.head e' = G.tail e}, a.x e'.1 e * globalVec G a e'.1 r := by
  rw [globalVec]

/-- **Page 16-18 of [elgamal2010].** The matrix `A_t(α)`: the estimate of the message symbol `r` at
node `t` has coefficient `transfer G a t r r'` on the message symbol `r'`. -/
def transfer (G : Multigraph V E) (a : LinCoeff K E b) (t : V) :
    Matrix (Σ j, Fin (b j)) (Σ j, Fin (b j)) K :=
  fun r r' => ∑ e : {e // G.head e = t}, a.z t e.1 r * globalVec G a e.1 r'

/-- Coefficients under a ring homomorphism. -/
def LinCoeff.map (φ : K →+* L) (a : LinCoeff K E b) : LinCoeff L E b :=
  ⟨fun r e => φ (a.y r e), fun e' e => φ (a.x e' e), fun t e r => φ (a.z t e r)⟩

lemma map_globalVec (G : Multigraph V E) (φ : K →+* L) (a : LinCoeff K E b) (e : E)
    (r : Σ j, Fin (b j)) : φ (globalVec G a e r) = globalVec G (a.map φ) e r := by
  induction hk : G.tail e using WellFoundedLT.induction generalizing e with
  | ind k ih =>
    rw [globalVec_eq, globalVec_eq, map_add, map_sum]
    congr 1
    · simp only [LinCoeff.map]
      split_ifs <;> simp
    · refine Finset.sum_congr rfl fun e' _ => ?_
      have hlt : G.tail e'.1 < k := (G.lt e'.1).trans_eq (e'.2.trans hk)
      rw [map_mul, ih _ hlt _ rfl]
      rfl

lemma map_transfer (G : Multigraph V E) (φ : K →+* L) (a : LinCoeff K E b) (t : V) :
    (transfer G a t).map φ = transfer G (a.map φ) t := by
  ext r r'
  simp only [Matrix.map_apply, transfer, map_sum, map_mul, map_globalVec]
  rfl

end Vec

/-! ### The generic coefficients -/

/-- **Page 16-20 of [elgamal2010].** The indeterminates: one for each coefficient of a linear
code. -/
abbrev LinVar (E : Type*) {V : Type*} (b : V → ℕ) :=
  ((Σ j, Fin (b j)) × E) ⊕ (E × E) ⊕ (V × E × (Σ j, Fin (b j)))

/-- The coefficients with values given by an assignment of the indeterminates. -/
def ofAssign (α : LinVar E b → K) : LinCoeff K E b :=
  ⟨fun r e => α (.inl (r, e)), fun e' e => α (.inr (.inl (e', e))),
    fun t e r => α (.inr (.inr (t, e, r)))⟩

/-- The assignment of the indeterminates given by coefficients. -/
def LinCoeff.assign (a : LinCoeff K E b) : LinVar E b → K :=
  Sum.elim (fun p => a.y p.1 p.2) (Sum.elim (fun p => a.x p.1 p.2) fun p => a.z p.1 p.2.1 p.2.2)

omit [LinearOrder V] [Fintype V] [Fintype E] in
@[simp] lemma ofAssign_assign (a : LinCoeff K E b) : ofAssign a.assign = a := rfl

/-- The coefficients of the linear code whose coefficients are indeterminates over `𝔽₂`. -/
def genericCoeff : LinCoeff (MvPolynomial (LinVar E b) (ZMod 2)) E b :=
  ofAssign MvPolynomial.X

/-- **Page 16-20 of [elgamal2010].** The polynomial `|A_t(x)|` in `𝔽₂[x]`. -/
def detGeneric (G : Multigraph V E) (t : V) : MvPolynomial (LinVar E b) (ZMod 2) :=
  (transfer G genericCoeff t).det

/-- Assigning values to the indeterminates of `|A_t(x)|` gives `|A_t(α)|`. -/
lemma aeval_detGeneric [CommRing K] [Algebra (ZMod 2) K] (G : Multigraph V E) (t : V)
    (α : LinVar E b → K) :
    MvPolynomial.aeval α (detGeneric (b := b) G t) = (transfer G (ofAssign α) t).det := by
  have hmap : (genericCoeff (E := E) (b := b)).map
      (MvPolynomial.aeval α : MvPolynomial (LinVar E b) (ZMod 2) →ₐ[ZMod 2] K).toRingHom =
      ofAssign α := by
    simp [LinCoeff.map, genericCoeff, ofAssign]
  have h := RingHom.map_det
    (MvPolynomial.aeval α : MvPolynomial (LinVar E b) (ZMod 2) →ₐ[ZMod 2] K).toRingHom
    (transfer G genericCoeff t)
  have h₂ : RingHom.mapMatrix
      (MvPolynomial.aeval α : MvPolynomial (LinVar E b) (ZMod 2) →ₐ[ZMod 2] K).toRingHom
      (transfer G genericCoeff t) = transfer G (ofAssign α) t := by
    rw [← hmap, ← map_transfer]
    rfl
  rw [h₂] at h
  exact h

/-! ### Routing is linear -/

section Routing

/-- **Page 16-21 of [elgamal2010].** Routing is a linear code over `𝔽₂` with `A_t(α) = I`. Suppose
every edge carries at most one bit, a bit on an edge out of a node either belongs to that node or
came in on another edge, and all bits reach `t`. -/
theorem exists_coeff_of_bit (G : Multigraph V E) (t : V) (bit : E → Option (Σ j, Fin (b j)))
    (hfwd : ∀ e r, bit e = some r → r.1 = G.tail e ∨ ∃ e', G.head e' = G.tail e ∧ bit e' = some r)
    (hdel : ∀ r : Σ j, Fin (b j), ∃ e, G.head e = t ∧ bit e = some r) :
    ∃ a : LinCoeff (ZMod 2) E b, transfer G a t = 1 := by
  classical
  choose dl hdl₁ hdl₂ using hdel
  let prev : E → (Σ j, Fin (b j)) → Option E := fun e r =>
    if h : ∃ e', G.head e' = G.tail e ∧ bit e' = some r then some (Classical.choose h) else none
  let a : LinCoeff (ZMod 2) E b :=
    ⟨fun r e => if bit e = some r then 1 else 0,
      fun e' e => if ∃ r, bit e = some r ∧ r.1 ≠ G.tail e ∧ prev e r = some e' then 1 else 0,
      fun _ e r => if e = dl r then 1 else 0⟩
  have hvec : ∀ e r', globalVec G a e r' = if bit e = some r' then 1 else 0 := by
    intro e r'
    induction hk : G.tail e using WellFoundedLT.induction generalizing e with
    | ind k ih =>
      rw [globalVec_eq]
      -- the sum over incoming edges
      have hsum : ∑ e' : {e' // G.head e' = G.tail e}, a.x e'.1 e * globalVec G a e'.1 r' =
          if ∃ r, bit e = some r ∧ r.1 ≠ G.tail e ∧ r = r' then 1 else 0 := by
        by_cases hcase : ∃ r, bit e = some r ∧ r.1 ≠ G.tail e
        · obtain ⟨r, hr, hrt⟩ := hcase
          have hex : ∃ e', G.head e' = G.tail e ∧ bit e' = some r :=
            (hfwd e r hr).resolve_left hrt
          have hprev : prev e r = some (Classical.choose hex) := by
            simp only [prev, dite_eq_left hex]
          set p := Classical.choose hex with hp
          obtain ⟨hp₁, hp₂⟩ : G.head p = G.tail e ∧ bit p = some r := Classical.choose_spec hex
          have hx : ∀ e' : {e' // G.head e' = G.tail e},
              a.x e'.1 e = if e'.1 = p then 1 else 0 := by
            intro e'
            simp only [a]
            by_cases he' : e'.1 = p
            · rw [ite_eq_left he', ite_eq_left ⟨r, hr, hrt, by rw [hprev, he']⟩]
            · rw [ite_eq_right he', ite_eq_right]
              rintro ⟨r₁, hr₁, -, hr₂⟩
              have : r₁ = r := by
                rw [hr] at hr₁
                exact (Option.some.inj hr₁).symm
              subst this
              rw [hprev] at hr₂
              exact he' (Option.some.inj hr₂).symm
          simp only [hx]
          rw [Finset.sum_eq_single (⟨p, hp₁⟩ : {e' // G.head e' = G.tail e})]
          · have hlt : G.tail p < k := (G.lt p).trans_eq (hp₁.trans hk)
            simp only [ite_true, one_mul]
            rw [ih _ hlt p rfl, hp₂]
            by_cases hrr : r = r'
            · subst hrr
              simp only [ite_true]
              rw [ite_eq_left ⟨r, hr, hrt, rfl⟩]
            · rw [ite_eq_right (by simpa using hrr), ite_eq_right]
              rintro ⟨r₁, hr₁, -, rfl⟩
              rw [hr] at hr₁
              exact hrr (Option.some.inj hr₁)
          · intro e' _ he'
            have : e'.1 ≠ p := fun h => he' (Subtype.ext h)
            simp [this]
          · simp
        · have hx : ∀ e' : {e' // G.head e' = G.tail e}, a.x e'.1 e = 0 := by
            intro e'
            simp only [a]
            rw [ite_eq_right]
            rintro ⟨r₁, hr₁, hr₂, -⟩
            exact hcase ⟨r₁, hr₁, hr₂⟩
          simp only [hx, zero_mul, Finset.sum_const_zero]
          rw [ite_eq_right]
          rintro ⟨r₁, hr₁, hr₂, -⟩
          exact hcase ⟨r₁, hr₁, hr₂⟩
      rw [hsum]
      simp only [a]
      by_cases hr' : bit e = some r'
      · by_cases htail : r'.1 = G.tail e
        · have hne : ¬ ∃ r, bit e = some r ∧ r.1 ≠ G.tail e ∧ r = r' := by
            rintro ⟨r₁, -, hr₂, rfl⟩
            exact hr₂ htail
          rw [ite_eq_right hne]
          simp [hr', htail]
        · have hex : ∃ r, bit e = some r ∧ r.1 ≠ G.tail e ∧ r = r' := ⟨r', hr', htail, rfl⟩
          rw [ite_eq_left hex]
          simp [hr', htail]
      · have hne : ¬ ∃ r, bit e = some r ∧ r.1 ≠ G.tail e ∧ r = r' := by
          rintro ⟨r₁, hr₁, -, rfl⟩
          exact hr' hr₁
        rw [ite_eq_right hne]
        simp [hr']
  refine ⟨a, ?_⟩
  ext r r'
  simp only [transfer]
  have hzz : ∀ e : {e // G.head e = t}, a.z t e.1 r = if e.1 = dl r then 1 else 0 := fun _ => rfl
  simp only [hzz, hvec]
  rw [Finset.sum_eq_single (⟨dl r, hdl₁ r⟩ : {e // G.head e = t})]
  · simp only [ite_true, one_mul, hdl₂ r, Option.some.injEq, Matrix.one_apply]
  · intro e _ he
    have : e.1 ≠ dl r := fun h => he (Subtype.ext h)
    simp [this]
  · simp

/-- The number of parallel edges from `k` to `l`. -/
def Multigraph.count (G : Multigraph V E) (k l : V) : ℕ :=
  #{e | G.tail e = k ∧ G.head e = l}

omit [Fintype V] in
lemma Multigraph.count_pos (G : Multigraph V E) (k l : V) (h : 0 < G.count k l) : k < l := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp h
  obtain ⟨rfl, rfl⟩ := (Finset.mem_filter.mp he).2
  exact G.lt e

/-- **Page 16-21 of [elgamal2010].** If all messages fit through the cuts separating them from `t`
then `|A_t(x)|` is a nonzero polynomial: by the max-flow min-cut theorem they can be routed to `t`,
and routing has `A_t(α) = I`. -/
theorem detGeneric_ne_zero_of_cuts (G : Multigraph V E) (t : V) (hb : b t = 0)
    (h : ∀ S : Finset V, t ∉ S →
      ∑ j ∈ S, (b j : ℤ) ≤ cutCap (fun j k => (G.count j k : ℤ)) S) :
    detGeneric (b := b) G t ≠ 0 := by
  classical
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := exists_routes (cap := G.count) G.count_pos b t h
  -- positions of the bits on the parallel edges
  have hpos : ∀ k l, Nonempty (↥(B k l) ↪ {e // G.tail e = k ∧ G.head e = l}) := by
    intro k l
    refine Function.Embedding.nonempty_of_card_le ?_
    rw [Fintype.card_coe, Fintype.card_subtype]
    exact hB₁ k l
  let pos : ∀ k l, ↥(B k l) ↪ {e // G.tail e = k ∧ G.head e = l} := fun k l => (hpos k l).some
  let bit : E → Option (Σ j, Fin (b j)) := fun e =>
    if h : ∃ r : ↥(B (G.tail e) (G.head e)), (pos _ _ r).1 = e then some (Classical.choose h).1
    else none
  have hbit₁ : ∀ e r, bit e = some r → r ∈ B (G.tail e) (G.head e) := by
    intro e r he
    simp only [bit] at he
    split_ifs at he with hex
    rw [← Option.some.inj he]
    exact (Classical.choose hex).2
  have hkey : ∀ r k l (hr : r ∈ B k l) (e : E), (pos k l ⟨r, hr⟩).1 = e → bit e = some r := by
    intro r k l hr e he
    have h₁ : G.tail e = k := he ▸ (pos k l ⟨r, hr⟩).2.1
    have h₂ : G.head e = l := he ▸ (pos k l ⟨r, hr⟩).2.2
    subst h₁ h₂
    have hex : ∃ r' : ↥(B (G.tail e) (G.head e)), (pos _ _ r').1 = e := ⟨⟨r, hr⟩, he⟩
    simp only [bit, dite_eq_left hex]
    have hspec : (pos _ _ (Classical.choose hex)).1 = e := Classical.choose_spec hex
    have : Classical.choose hex = ⟨r, hr⟩ :=
      (pos _ _).injective (Subtype.ext (hspec.trans he.symm))
    rw [this]
  have hbit₂ : ∀ k l, ∀ r ∈ B k l, ∃ e, G.tail e = k ∧ G.head e = l ∧ bit e = some r :=
    fun k l r hr => ⟨(pos k l ⟨r, hr⟩).1, (pos k l ⟨r, hr⟩).2.1, (pos k l ⟨r, hr⟩).2.2,
      hkey r k l hr _ rfl⟩
  obtain ⟨a, ha⟩ := exists_coeff_of_bit G t bit
    (fun e r he => by
      rcases hB₂ _ _ r (hbit₁ e r he) with h' | ⟨j, -, hj⟩
      · exact Or.inl h'
      · obtain ⟨e', -, he₂, he₃⟩ := hbit₂ _ _ r hj
        exact Or.inr ⟨e', he₂, he₃⟩)
    (fun r => by
      have hrt : r.1 ≠ t := by
        intro hrt
        have hi := r.2.2
        have hbr : b r.1 = 0 := by rw [hrt]; exact hb
        omega
      obtain ⟨i, -, hi⟩ := hB₃ r hrt
      obtain ⟨e, -, he₂, he₃⟩ := hbit₂ _ _ r hi
      exact ⟨e, he₂, he₃⟩)
  intro h0
  have h1 := aeval_detGeneric G t a.assign
  rw [h0, map_zero, ofAssign_assign, ha, Matrix.det_one] at h1
  exact zero_ne_one h1

end Routing

/-! ### The code of the coefficients -/

section Code

variable {F : Type*} [Field F]

/-- **Pages 16-17 and 16-19 of [elgamal2010].** The linear code with coefficients `a`. An edge
alphabet is the tuple of the symbols of the parallel edges, and a decoder multiplies by the inverse
of `A_l(α)`. -/
def LinCoeff.code (G : Multigraph V E) (a : LinCoeff F E b) :
    NetCode V (fun k l => {e // G.tail e = k ∧ G.head e = l} → F) (fun j => Fin (b j) → F) where
  enc k _ u mk := fun e =>
    ∑ i : Fin (b k), a.y ⟨k, i⟩ e.1 * mk i +
      ∑ e' : {e' // G.head e' = k}, a.x e'.1 e.1 *
        u (G.tail e'.1) ((G.lt e'.1).trans_eq e'.2) ⟨e'.1, rfl, e'.2⟩
  dec l j u := fun i =>
    Matrix.mulVec (transfer G a l)⁻¹ (fun r => ∑ e : {e // G.head e = l}, a.z l e.1 r *
      u (G.tail e.1) ((G.lt e.1).trans_eq e.2) ⟨e.1, rfl, e.2⟩) ⟨j, i⟩

/-- The symbol on an edge is the linear combination of the message symbols given by the global
coding vector. -/
lemma LinCoeff.code_edge (G : Multigraph V E) (a : LinCoeff F E b) (m : ∀ j, Fin (b j) → F)
    (k : V) : ∀ (l : V) (e : {e // G.tail e = k ∧ G.head e = l}),
      (a.code G).edge m k l e = ∑ r : Σ j, Fin (b j), globalVec G a e.1 r * m r.1 r.2 := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    rintro _ ⟨e, rfl, rfl⟩
    rw [NetCode.edge_eq]
    change ∑ i : Fin (b (G.tail e)), a.y ⟨G.tail e, i⟩ e * m (G.tail e) i +
      ∑ e' : {e' // G.head e' = G.tail e}, a.x e'.1 e *
        (a.code G).edge m (G.tail e'.1) (G.tail e) ⟨e'.1, rfl, e'.2⟩ = _
    have hin : ∀ e' : {e' // G.head e' = G.tail e},
        (a.code G).edge m (G.tail e'.1) (G.tail e) ⟨e'.1, rfl, e'.2⟩ =
          ∑ r : Σ j, Fin (b j), globalVec G a e'.1 r * m r.1 r.2 := fun e' =>
      ih _ ((G.lt e'.1).trans_eq e'.2) _ ⟨e'.1, rfl, e'.2⟩
    have hv : ∀ r, globalVec G a e r = (if r.1 = G.tail e then a.y r e else 0) +
        ∑ e' : {e' // G.head e' = G.tail e}, a.x e'.1 e * globalVec G a e'.1 r :=
      globalVec_eq G a e
    simp only [hin, hv, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    · rw [Fintype.sum_sigma, Finset.sum_eq_single (G.tail e)]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    · rw [Finset.sum_comm]

/-- **Page 16-19 of [elgamal2010].** If `A_l(α)` is invertible for every destination then the linear
code has no errors. -/
theorem LinCoeff.code_correct (G : Multigraph V E) (a : LinCoeff F E b) {D : V → Finset V}
    (h : ∀ j, ∀ l ∈ D j, (transfer G a l).det ≠ 0) (m : ∀ j, Fin (b j) → F) :
    (a.code G).Correct D m := by
  intro j l hl
  funext i
  have hrecv : (fun r => ∑ e : {e // G.head e = l}, a.z l e.1 r *
      (a.code G).edge m (G.tail e.1) l ⟨e.1, rfl, e.2⟩) =
      Matrix.mulVec (transfer G a l) fun r => m r.1 r.2 := by
    funext r
    simp only [LinCoeff.code_edge, Matrix.mulVec, dotProduct, transfer, Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hdet : IsUnit (transfer G a l).det := isUnit_iff_ne_zero.mpr (h j l hl)
  change Matrix.mulVec (transfer G a l)⁻¹ (fun r => ∑ e : {e // G.head e = l}, a.z l e.1 r *
    (a.code G).edge m (G.tail e.1) l ⟨e.1, rfl, e.2⟩) ⟨j, i⟩ = m j i
  rw [hrecv, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

/-- **Page 16-21 of [elgamal2010].** If `|A_t(x)|` is a nonzero polynomial then the cut conditions
hold: a linear code with invertible `A_t(α)` exists over a large field, and the cutset bound applies
to it. -/
theorem cuts_of_detGeneric_ne_zero (G : Multigraph V E) {t : V}
    (h : detGeneric (b := b) G t ≠ 0) {S : Finset V} (ht : t ∉ S) :
    ∑ j ∈ S, (b j : ℤ) ≤ cutCap (fun j k => (G.count j k : ℤ)) S := by
  classical
  obtain ⟨m₀, hm₀⟩ := exists_aeval_galoisField_ne_zero h
  obtain ⟨α, hα⟩ := hm₀ (m₀ + 1) (Nat.le_succ _)
  rw [aeval_detGeneric] at hα
  let _ : Fintype (GaloisField 2 (m₀ + 1)) := Fintype.ofFinite _
  have hq : 1 < Fintype.card (GaloisField 2 (m₀ + 1)) := Fintype.one_lt_card
  have hcor := LinCoeff.code_correct G (ofAssign α) (D := fun _ => {t})
    (fun j l hl => by rwa [Finset.mem_singleton.mp hl])
  have hb := NetCode.cut_bound ((ofAssign α).code G) (fun _ => {t}) S
  rw [NetCode.errProb_eq_zero _ hcor, sub_zero, one_mul] at hb
  have hsrc : cutSources (fun _ : V => ({t} : Finset V)) S = S := by
    refine Finset.filter_true_of_mem fun j _ => ⟨t, ?_⟩
    simp [ht]
  rw [hsrc] at hb
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Fintype.card_subtype] at hb
  have hL : (∏ j ∈ S, (Fintype.card (GaloisField 2 (m₀ + 1)) : ℝ) ^ b j) =
      (Fintype.card (GaloisField 2 (m₀ + 1)) : ℝ) ^ ∑ j ∈ S, b j := Finset.prod_pow_eq_pow_sum _ _ _
  have hR : (∏ j ∈ S, ∏ k ∈ Sᶜ, (Fintype.card (GaloisField 2 (m₀ + 1)) : ℝ) ^ G.count j k) =
      (Fintype.card (GaloisField 2 (m₀ + 1)) : ℝ) ^ ∑ j ∈ S, ∑ k ∈ Sᶜ, G.count j k := by
    simp only [Finset.prod_pow_eq_pow_sum]
  have hb' : (Fintype.card (GaloisField 2 (m₀ + 1)) : ℝ) ^ ∑ j ∈ S, b j ≤
      (Fintype.card (GaloisField 2 (m₀ + 1)) : ℝ) ^ ∑ j ∈ S, ∑ k ∈ Sᶜ, G.count j k := by
    rw [← hL, ← hR]
    convert hb using 6
    rfl
  have hle := (pow_le_pow_iff_right₀ (by exact_mod_cast hq)).mp hb'
  simp only [cutCap]
  exact_mod_cast hle

open Classical in
/-- **Page 16-22 of [elgamal2010].** A random linear code works with high probability: if `|A_t(x)|`
is nonzero for all `t ∈ T` then the fraction of the coefficient vectors over a finite field `F` for
which some `A_t(α)` is not invertible is at most `deg ∏ |A_t(x)| / |F|`. -/
theorem card_not_invertible_le [Algebra (ZMod 2) F] [Fintype F] (G : Multigraph V E)
    {T : Finset V} (h : ∀ t ∈ T, detGeneric (b := b) G t ≠ 0) :
    (#{α : LinVar E b → F | ∃ t ∈ T, (transfer G (ofAssign α) t).det = 0} : ℝ) /
        (Fintype.card F : ℝ) ^ Fintype.card (LinVar E b) ≤
      ((∏ t ∈ T, detGeneric (b := b) G t).totalDegree : ℝ) / Fintype.card F := by
  have hP : ∏ t ∈ T, detGeneric (b := b) G t ≠ 0 := Finset.prod_ne_zero_iff.mpr h
  have hset : (Finset.univ.filter fun α : LinVar E b → F =>
      ∃ t ∈ T, (transfer G (ofAssign α) t).det = 0) =
      Finset.univ.filter fun α : LinVar E b → F =>
        MvPolynomial.aeval α (∏ t ∈ T, detGeneric (b := b) G t) = 0 := by
    refine Finset.filter_congr fun α _ => ?_
    rw [map_prod, Finset.prod_eq_zero_iff]
    simp only [aeval_detGeneric]
  rw [hset]
  exact card_aeval_eq_zero_le (F := F) hP

end Code

/-! ### The size of the field -/

section Degree

open MvPolynomial

/-- The indeterminates of the encoders of edges out of nodes above `k`, and those of the
decoders. -/
def varAfter (G : Multigraph V E) (k : V) : LinVar E b → Prop
  | .inl p => k < G.tail p.2
  | .inr (.inl p) => k < G.tail p.2
  | .inr (.inr _) => True

omit [Fintype V] [Fintype E] in
lemma varAfter_mono (G : Multigraph V E) {k k' : V} (h : k' ≤ k) {v : LinVar E b}
    (hv : varAfter G k v) : varAfter G k' v := by
  rcases v with p | p | p
  · exact h.trans_lt hv
  · exact h.trans_lt hv
  · trivial

/-- The symbol on an edge does not involve the indeterminates of the later encoders or the decoders.
-/
lemma degreeOf_globalVec_eq_zero (G : Multigraph V E) (e : E) (r : Σ j, Fin (b j))
    {v : LinVar E b} (hv : varAfter G (G.tail e) v) :
    degreeOf v (globalVec G (genericCoeff (E := E) (b := b)) e r) = 0 := by
  induction hk : G.tail e using WellFoundedLT.induction generalizing e with
  | ind k ih =>
    subst hk
    rw [globalVec_eq]
    refine Nat.le_zero.mp ((degreeOf_add_le _ _ _).trans (max_le ?_ ?_))
    · split_ifs
      · refine (degreeOf_X_of_ne ?_).le
        rintro rfl
        exact lt_irrefl _ hv
      · simp
    · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e' _ => ?_)
      refine (degreeOf_mul_le _ _ _).trans ?_
      have hne : v ≠ .inr (.inl (e'.1, e)) := by
        rintro rfl
        exact lt_irrefl _ hv
      have hlt : G.tail e'.1 < G.tail e := (G.lt e'.1).trans_eq e'.2
      have h₁ : degreeOf v ((genericCoeff (E := E) (b := b)).x e'.1 e) = 0 := degreeOf_X_of_ne hne
      rw [h₁, ih _ hlt e'.1 (varAfter_mono G hlt.le hv) rfl]

/-- Each indeterminate appears at most once along a path, so a global coding vector has degree at
most `1` in it. -/
lemma degreeOf_globalVec_le (G : Multigraph V E) (e : E) (r : Σ j, Fin (b j)) (v : LinVar E b) :
    degreeOf v (globalVec G (genericCoeff (E := E) (b := b)) e r) ≤ 1 := by
  classical
  induction hk : G.tail e using WellFoundedLT.induction generalizing e with
  | ind k ih =>
    subst hk
    rw [globalVec_eq]
    refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · split_ifs
      · rw [show (genericCoeff (E := E) (b := b)).y r e = X (.inl (r, e)) from rfl, degreeOf_X]
        split_ifs <;> simp
      · simp
    · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e' _ => ?_)
      refine (degreeOf_mul_le _ _ _).trans ?_
      have hlt : G.tail e'.1 < G.tail e := (G.lt e'.1).trans_eq e'.2
      by_cases hv : v = .inr (.inl (e'.1, e))
      · have h₂ : degreeOf v (globalVec G (genericCoeff (E := E) (b := b)) e'.1 r) = 0 :=
          degreeOf_globalVec_eq_zero G e'.1 r (by subst hv; exact hlt)
        rw [h₂, add_zero, show (genericCoeff (E := E) (b := b)).x e'.1 e =
          X (.inr (.inl (e'.1, e))) from rfl, degreeOf_X]
        split_ifs <;> simp
      · have h₁ : degreeOf v ((genericCoeff (E := E) (b := b)).x e'.1 e) = 0 := degreeOf_X_of_ne hv
        rw [h₁, zero_add]
        exact ih _ hlt e'.1 rfl

/-- **Page 16-22 of [elgamal2010].** The polynomial `|A_t(x)|` has degree at most `R` in each
indeterminate. -/
lemma degreeOf_detGeneric_le (G : Multigraph V E) (t : V) (v : LinVar E b) :
    degreeOf v (detGeneric (b := b) G t) ≤ Fintype.card (Σ j, Fin (b j)) := by
  classical
  have hentry : ∀ r r', degreeOf v (transfer G (genericCoeff (E := E) (b := b)) t r r') ≤ 1 := by
    intro r r'
    refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun e _ => ?_)
    refine (degreeOf_mul_le _ _ _).trans ?_
    by_cases hv : v = .inr (.inr (t, e.1, r))
    · have h₂ : degreeOf v (globalVec G (genericCoeff (E := E) (b := b)) e.1 r') = 0 :=
        degreeOf_globalVec_eq_zero G e.1 r' (by subst hv; trivial)
      rw [h₂, add_zero, show (genericCoeff (E := E) (b := b)).z t e.1 r =
        X (.inr (.inr (t, e.1, r))) from rfl, degreeOf_X]
      split_ifs <;> simp
    · have h₁ : degreeOf v ((genericCoeff (E := E) (b := b)).z t e.1 r) = 0 := degreeOf_X_of_ne hv
      rw [h₁, zero_add]
      exact degreeOf_globalVec_le G e.1 r' v
  unfold detGeneric
  rw [Matrix.det_apply']
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have hsign : ∀ n : ℤ, degreeOf v (n : MvPolynomial (LinVar E b) (ZMod 2)) = 0 := by
    intro n
    rw [← map_intCast (C : ZMod 2 →+* MvPolynomial (LinVar E b) (ZMod 2)) n]
    exact degreeOf_C _ _
  rw [hsign, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc _ ≤ ∑ _i : Σ j, Fin (b j), 1 := Finset.sum_le_sum fun i _ => hentry _ _
    _ = _ := by simp

/-- **Page 16-22 of [elgamal2010].** A field with more than `|D| R` elements is enough: then a
single coefficient vector makes `A_t(α)` invertible for all destinations. So `𝔽_{2^m}` with
`m ≤ ⌈log(|D| R + 1)⌉` works. -/
theorem exists_coeff_of_card_gt {F : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype F]
    (G : Multigraph V E) {T : Finset V} (h : ∀ t ∈ T, detGeneric (b := b) G t ≠ 0)
    (hF : #T * Fintype.card (Σ j, Fin (b j)) < Fintype.card F) :
    ∃ α : LinVar E b → F, ∀ t ∈ T, (transfer G (ofAssign α) t).det ≠ 0 := by
  have hP : ∏ t ∈ T, detGeneric (b := b) G t ≠ 0 := Finset.prod_ne_zero_iff.mpr h
  obtain ⟨α, hα⟩ := exists_aeval_ne_zero_of_degreeOf (F := F) hP fun v => by
    refine lt_of_le_of_lt ((degreeOf_prod_le _ _ _).trans ?_) hF
    calc _ ≤ ∑ _t ∈ T, Fintype.card (Σ j, Fin (b j)) :=
          Finset.sum_le_sum fun t _ => degreeOf_detGeneric_le G t v
      _ = _ := by simp
  refine ⟨α, fun t ht => ?_⟩
  rw [map_prod] at hα
  rw [← aeval_detGeneric]
  exact Finset.prod_ne_zero_iff.mp hα t ht

end Degree

end InfoTheory
