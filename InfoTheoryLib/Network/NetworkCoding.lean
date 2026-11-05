/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.LinearNetworkCode

/-!
# The network coding theorem

The capacity of a noiseless multicast network is the cutset bound, and linear codes achieve it with
zero error. More generally, the capacity region of a network in which every destination wants all
the messages is the cutset outer bound.

## Main definitions

* `capGraph`: the multigraph of integer capacities.

## Main statements

* `detGeneric_ne_zero_iff`: `|A_t(x)| ≠ 0` if and only if the cut conditions hold.
* `exists_linear_code`: integer rates inside the cut conditions of a multigraph are achieved by a
  linear code over any field with more than `|D| R` elements.
* `isAchievableZE_of_cuts`: linear codes achieve all rates inside the cut conditions.
* `network_coding_theorem`: the **network coding theorem** of Lecture 16 of El Gamal and Kim.
* `capacityRegion_multisource`: the capacity region of a multi-source multicast network.

## Implementation notes

The notes approximate real capacities by a multigraph whose edges carry `n/k` bits. Here a
  multigraph
with `⌊K C⌋` edges is fixed, with `K` large, and for block length `n` the field `𝔽_{2^m}` with
`m = ⌊n / K⌋` is used. So all large `n` are covered by one construction, because a nonzero
  polynomial
has a nonzero value in `𝔽_{2^m}` for all large `m`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 16
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {V : Type*} [LinearOrder V] [Fintype V]

/-- The multigraph with `cap j k` parallel edges from `j` to `k`. -/
def capGraph (cap : V → V → ℕ) (h : ∀ j k, 0 < cap j k → j < k) :
    Multigraph V (Σ p : V × V, Fin (cap p.1 p.2)) :=
  ⟨fun e => e.1.1, fun e => e.1.2, fun e => h _ _ (Fin.pos e.2)⟩

lemma capGraph_count (cap : V → V → ℕ) (h : ∀ j k, 0 < cap j k → j < k) (k l : V) :
    (capGraph cap h).count k l = cap k l := by
  have : (Finset.univ.filter fun e : Σ p : V × V, Fin (cap p.1 p.2) =>
      (capGraph cap h).tail e = k ∧ (capGraph cap h).head e = l) =
      Finset.univ.map ⟨Sigma.mk (k, l), sigma_mk_injective⟩ := by
    ext ⟨⟨a, c⟩, i⟩
    constructor
    · intro h
      obtain ⟨rfl, rfl⟩ := (Finset.mem_filter.mp h).2
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · intro h
      obtain ⟨x, -, hx⟩ := Finset.mem_map.mp h
      cases hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩
  unfold Multigraph.count
  rw [this]
  simp

/-- **Page 16-21 of [elgamal2010].** For a multigraph, `|A_t(x)|` is a nonzero polynomial if and
  only
if all the message symbols fit through the cuts separating them from `t`. -/
theorem detGeneric_ne_zero_iff {E : Type*} [Fintype E] (G : Multigraph V E) {b : V → ℕ}
    {t : V} (hb : b t = 0) :
    detGeneric (b := b) G t ≠ 0 ↔ ∀ S : Finset V, t ∉ S →
      ∑ j ∈ S, (b j : ℤ) ≤ cutCap (fun j k => (G.count j k : ℤ)) S :=
  ⟨fun h _ hS => cuts_of_detGeneric_ne_zero G h hS, detGeneric_ne_zero_of_cuts G t hb⟩

/-- **Pages 16-15 and 16-22 of [elgamal2010].** Linear network coding with zero error and finite
  block
size: if the destinations in `T` have no messages and the integer rates fit through the cuts of a
multigraph, then a linear code over any field `F` with `|F| > |T| R`, of characteristic `2`, has no
errors. -/
theorem exists_linear_code {E F : Type*} [Fintype E] [Field F] [Algebra (ZMod 2) F]
    [Fintype F] (G : Multigraph V E) {b : V → ℕ} {T : Finset V} {D : V → Finset V}
    (hD : ∀ j, ∀ l ∈ D j, l ∈ T) (hb : ∀ t ∈ T, b t = 0)
    (h : ∀ t ∈ T, ∀ S : Finset V, t ∉ S →
      ∑ j ∈ S, (b j : ℤ) ≤ cutCap (fun j k => (G.count j k : ℤ)) S)
    (hF : #T * Fintype.card (Σ j, Fin (b j)) < Fintype.card F) :
    ∃ a : LinCoeff F E b, ∀ m, (a.code G).Correct D m := by
  obtain ⟨α, hα⟩ := exists_coeff_of_card_gt (F := F) G
    (fun t ht => detGeneric_ne_zero_of_cuts G t (hb t ht) (h t ht)) hF
  exact ⟨ofAssign α, LinCoeff.code_correct G _ fun j l hl => hα l (hD j l hl)⟩

/-- A point is in the closure of a set if all its multiples by `θ < 1` are in the set. -/
lemma mem_closure_of_forall_smul {X : Type*} [AddCommMonoid X] [Module ℝ X] [TopologicalSpace X]
    [ContinuousSMul ℝ X] {A : Set X} {x : X} (h : ∀ θ : ℝ, 0 < θ → θ < 1 → θ • x ∈ A) :
    x ∈ closure A := by
  have h₁ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h₂ : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h₁
  have hlim : Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2)) • x) atTop (𝓝 x) := by
    simpa using h₂.smul_const x
  refine mem_closure_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine h _ ?_ ?_
  · have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one hn]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  · have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith

/-- A positive integer scale for which the integer cut conditions hold. -/
private lemma exists_scale (N : NoiselessNetwork V) {T : Finset V} {R : V → ℝ}
    (h0 : ∀ j, 0 ≤ R j)
    (hcut : ∀ t ∈ T, ∀ S : Finset V, t ∉ S → ∑ j ∈ S, R j = 0 ∨ ∑ j ∈ S, R j < cutCap N.C S) :
    ∃ K : ℕ, 0 < K ∧ ∀ t ∈ T, ∀ S : Finset V, t ∉ S →
      ∑ j ∈ S, (((if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1 : ℕ)) : ℤ) ≤
        cutCap (fun j k => ((⌊(K : ℝ) * N.C j k⌋₊ : ℕ) : ℤ)) S := by
  have hev : ∀ S : Finset V, ∀ᶠ K : ℕ in atTop, ∀ t ∈ T, t ∉ S →
      ∑ j ∈ S, (((if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1 : ℕ)) : ℤ) ≤
        cutCap (fun j k => ((⌊(K : ℝ) * N.C j k⌋₊ : ℕ) : ℤ)) S := by
    intro S
    have hpos : ∀ K : ℕ, (0 : ℤ) ≤ cutCap (fun j k => ((⌊(K : ℝ) * N.C j k⌋₊ : ℕ) : ℤ)) S :=
      fun K => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _
    by_cases hS : ∃ t ∈ T, t ∉ S
    · obtain ⟨t, ht, htS⟩ := hS
      rcases hcut t ht S htS with hz | hlt
      · refine Eventually.of_forall fun K _ _ _ => ?_
        have hzero : ∀ j ∈ S, R j = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun j _ => h0 j).mp hz
        rw [Finset.sum_eq_zero fun j hj => by simp [hzero j hj]]
        exact hpos K
      · have hgap : 0 < cutCap N.C S - ∑ j ∈ S, R j := sub_pos.mpr hlt
        have hev' : ∀ᶠ K : ℕ in atTop, (Fintype.card V : ℝ) ^ 2 + Fintype.card V ≤
            (K : ℝ) * (cutCap N.C S - ∑ j ∈ S, R j) :=
          tendsto_natCast_atTop_atTop.atTop_mul_const hgap |>.eventually_ge_atTop _
        filter_upwards [hev'] with K hK _ _ _
        have h₁ := cutCap_floor_ge N.C K S
        have hle : ∑ j ∈ S, (((if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1 : ℕ) : ℕ) : ℝ) ≤
            (K : ℝ) * ∑ j ∈ S, R j + Fintype.card V := by
          have hterm : ∀ j ∈ S, (((if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1 : ℕ) : ℕ) : ℝ) ≤
              (K : ℝ) * R j + 1 := by
            intro j _
            have hK0 : (0 : ℝ) ≤ (K : ℝ) * R j := mul_nonneg (Nat.cast_nonneg _) (h0 j)
            split_ifs with hj
            · push_cast
              linarith
            · push_cast
              linarith [Nat.floor_le hK0]
          calc _ ≤ ∑ j ∈ S, ((K : ℝ) * R j + 1) := Finset.sum_le_sum hterm
            _ = (K : ℝ) * ∑ j ∈ S, R j + #S := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
              simp
            _ ≤ _ := by
              have : (#S : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ S
              linarith
        have hfin : ((∑ j ∈ S, (((if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1 : ℕ)) : ℤ) : ℤ) : ℝ) ≤
            ((cutCap (fun j k => ((⌊(K : ℝ) * N.C j k⌋₊ : ℕ) : ℤ)) S : ℤ) : ℝ) := by
          have hcast : ((∑ j ∈ S, (((if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1 : ℕ)) : ℤ) : ℤ) :
              ℝ) = ∑ j ∈ S, (((if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1 : ℕ) : ℕ) : ℝ) := by
            push_cast
            rfl
          rw [hcast]
          have hmul : (K : ℝ) * (cutCap N.C S - ∑ j ∈ S, R j) =
              (K : ℝ) * cutCap N.C S - (K : ℝ) * ∑ j ∈ S, R j := by ring
          linarith
        exact_mod_cast hfin
    · push Not at hS
      exact Eventually.of_forall fun K t ht htS => absurd (hS t ht) htS
  obtain ⟨K, hK₁, hK₂⟩ := ((eventually_all.mpr hev).and (eventually_gt_atTop 0)).exists.imp
    fun K h => And.intro h.2 h.1
  exact ⟨K, hK₁, fun t ht S htS => hK₂ S t ht htS⟩

/-- **Page 16-22 of [elgamal2010], for several sources.** If `T` contains all destinations and has
no messages, and all rates are inside the cut conditions, then linear codes achieve the rates with
zero error. A cut whose sources have rate `0` needs no strict inequality. -/
theorem isAchievableZE_of_cuts (N : NoiselessNetwork V) {T : Finset V} {D : V → Finset V}
    (hD : ∀ j, ∀ l ∈ D j, l ∈ T) {R : V → ℝ} (h0 : ∀ j, 0 ≤ R j) (hT : ∀ t ∈ T, R t = 0)
    (hcut : ∀ t ∈ T, ∀ S : Finset V, t ∉ S → ∑ j ∈ S, R j = 0 ∨ ∑ j ∈ S, R j < cutCap N.C S) :
    IsAchievableZE N D R := by
  classical
  refine ⟨h0, ?_⟩
  obtain ⟨K, hK, hscale⟩ := exists_scale N h0 hcut
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  let cap : V → V → ℕ := fun j k => ⌊(K : ℝ) * N.C j k⌋₊
  have hcap : ∀ j k, 0 < cap j k → j < k := floor_acyclic N.acyclic (Nat.cast_nonneg K)
  let b : V → ℕ := fun j => if R j = 0 then 0 else ⌊(K : ℝ) * R j⌋₊ + 1
  let G := capGraph cap hcap
  have hdet : ∀ t ∈ T, detGeneric (b := b) G t ≠ 0 := by
    intro t ht
    refine detGeneric_ne_zero_of_cuts G t (by simp [b, hT t ht]) fun S htS => ?_
    have hcount : (fun j k => (G.count j k : ℤ)) = fun j k => ((cap j k : ℕ) : ℤ) := by
      funext j k
      rw [capGraph_count]
    rw [hcount]
    exact hscale t ht S htS
  have hP : ∏ t ∈ T, detGeneric (b := b) G t ≠ 0 := Finset.prod_ne_zero_iff.mpr hdet
  obtain ⟨m₀, hm₀⟩ := exists_aeval_galoisField_ne_zero hP
  -- for large `n`, the field of size `2 ^ (n / K)` works
  have hdiv : Tendsto (fun n : ℕ => n / K) atTop atTop :=
    Nat.tendsto_div_const_atTop hK.ne'
  have hmsg : ∀ j, ∀ᶠ n : ℕ in atTop, ⌈(n : ℝ) * R j⌉₊ ≤ (n / K) * b j := by
    intro j
    by_cases hj : R j = 0
    · exact Eventually.of_forall fun n => by simp [hj]
    · have hb : (K : ℝ) * R j < (b j : ℝ) := by
        simp only [b, hj, ite_false]
        push_cast
        exact Nat.lt_floor_add_one _
      have hgap : 0 < (b j : ℝ) / K - R j := by
        rw [sub_pos, lt_div_iff₀ hK']
        linarith
      have hev : ∀ᶠ n : ℕ in atTop, (b j : ℝ) ≤ (n : ℝ) * ((b j : ℝ) / K - R j) :=
        tendsto_natCast_atTop_atTop.atTop_mul_const hgap |>.eventually_ge_atTop _
      filter_upwards [hev] with n hn
      refine Nat.ceil_le.mpr ?_
      have hlt : (n : ℝ) / K < ((n / K : ℕ) : ℝ) + 1 := by
        have h₀ : n < K * (n / K + 1) := Nat.lt_mul_div_succ n hK
        have h₀' : (n : ℝ) < K * (((n / K : ℕ) : ℝ) + 1) := by exact_mod_cast h₀
        rw [div_lt_iff₀ hK']
        linarith
      have hbpos : (0 : ℝ) ≤ b j := Nat.cast_nonneg _
      have h₁ : (n : ℝ) / K * (b j : ℝ) ≤ (((n / K : ℕ) : ℝ) + 1) * (b j : ℝ) :=
        mul_le_mul_of_nonneg_right hlt.le hbpos
      have h₂ : (n : ℝ) * ((b j : ℝ) / K - R j) = (n : ℝ) / K * (b j : ℝ) - (n : ℝ) * R j := by
        ring
      push_cast
      nlinarith
  filter_upwards [eventually_all.mpr hmsg, hdiv.eventually_ge_atTop (m₀ + 1)] with n hn₁ hn₂
  set m := n / K with hm
  have hm0 : m ≠ 0 := by omega
  obtain ⟨α, hα⟩ := hm₀ m (by omega)
  let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m hm0]
  have hinv : ∀ t ∈ T, (transfer G (ofAssign α) t).det ≠ 0 := by
    intro t ht
    rw [map_prod] at hα
    rw [← aeval_detGeneric]
    exact Finset.prod_ne_zero_iff.mp hα t ht
  have hcor := LinCoeff.code_correct G (ofAssign α) (D := D)
    fun j l hl => hinv l (hD j l hl)
  have hμ : ∀ j, Nonempty (Fin (2 ^ ⌈(n : ℝ) * R j⌉₊) ↪ (Fin (b j) → GaloisField 2 m)) := by
    intro j
    refine Function.Embedding.nonempty_of_card_le ?_
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hq, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (hn₁ j)
  have hι : ∀ k l, Nonempty (({e // G.tail e = k ∧ G.head e = l} → GaloisField 2 m) ↪
      Fin (2 ^ ⌊(n : ℝ) * N.C k l⌋₊)) := by
    intro k l
    refine Function.Embedding.nonempty_of_card_le ?_
    rw [Fintype.card_fun, Fintype.card_fin, hq, ← pow_mul, Fintype.card_subtype]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have hc : #{e | G.tail e = k ∧ G.head e = l} = cap k l := capGraph_count cap hcap k l
    rw [hc]
    refine Nat.le_floor ?_
    have h₁ : ((n / K : ℕ) : ℝ) ≤ (n : ℝ) / K := Nat.cast_div_le
    have h₂ : ((cap k l : ℕ) : ℝ) ≤ (K : ℝ) * N.C k l :=
      Nat.floor_le (mul_nonneg hK'.le (N.nonneg k l))
    push_cast
    calc ((n / K : ℕ) : ℝ) * ((cap k l : ℕ) : ℝ)
        ≤ (n : ℝ) / K * ((K : ℝ) * N.C k l) :=
          mul_le_mul h₁ h₂ (Nat.cast_nonneg _) (by positivity)
      _ = (n : ℝ) * N.C k l := by
          field_simp
  exact ((ofAssign α).code G).exists_relabel hcor (fun j => (hμ j).some)
    (fun j => (hμ j).some.injective) (fun k l => (hι k l).some)
    (fun k l => (hι k l).some.injective.injOn)

/-- **Network coding theorem, page 16-15 of [elgamal2010].** The capacity of a noiseless multicast
network is the cutset bound, and it is achieved with zero error by linear network codes. -/
theorem network_coding_theorem (N : NoiselessNetwork V) {s : V} {T : Finset V} (hs : s ∉ T)
    (hT : T.Nonempty) :
    multicastCapacity N s T = T.inf' hT (minCut N.C s) := by
  refine multicastCapacity_eq (fun R hR hlt => ?_) (fun R h => ?_)
  · refine (isAchievableZE_of_cuts N (T := T) (fun j l hl => ?_) (fun j => ?_) (fun t ht => ?_)
      fun t ht S htS => ?_).isAchievable
    · by_cases hj : j = s
      · simpa [multicastD, hj] using hl
      · simp [multicastD, hj] at hl
    · simp only [singleRate]
      split_ifs <;> simp [hR]
    · have : t ≠ s := fun h => hs (h ▸ ht)
      simp [singleRate, this]
    · by_cases hsS : s ∈ S
      · refine Or.inr ?_
        rw [Finset.sum_eq_single_of_mem s hsS fun j _ hj => by simp [singleRate, hj]]
        have h₁ : R < minCut N.C s t := (Finset.lt_inf'_iff _).mp hlt t ht
        simpa [singleRate] using h₁.trans_le (minCut_le N.C hsS htS)
      · refine Or.inl (Finset.sum_eq_zero fun j hj => ?_)
        have : j ≠ s := fun h => hsS (h ▸ hj)
        simp [singleRate, this]
  · refine (Finset.le_inf'_iff _ _).mpr fun t ht => ?_
    exact h.le_minCut ht fun h' => hs (h' ▸ ht)

/-- **Page 16-25 of [elgamal2010].** The capacity region of a multi-source multicast network: the
nodes of `Src` are the sources and every node of `T` wishes to decode all the messages. For rate
tuples with no rate outside `Src`, the capacity region is the cutset outer bound. The notes cite
  this
result; here it comes from the same proof as the network coding theorem. -/
theorem capacityRegion_multisource (N : NoiselessNetwork V) {Src T : Finset V}
    (hdisj : Disjoint Src T) {R : V → ℝ} (hR : ∀ j, j ∉ Src → R j = 0) :
    R ∈ capacityRegion N (fun j => if j ∈ Src then T else ∅) ↔
      R ∈ cutsetRegion N (fun j => if j ∈ Src then T else ∅) := by
  refine ⟨fun h => capacityRegion_subset_cutsetRegion N _ h, fun h => ?_⟩
  obtain ⟨h0, hS⟩ := h
  -- all multiples `θ R`, with `0 < θ < 1`, are achievable
  have hach : ∀ θ : ℝ, 0 < θ → θ < 1 →
      IsAchievable N (fun j => if j ∈ Src then T else ∅) fun j => θ * R j := by
    intro θ hθ hθ₁
    refine (isAchievableZE_of_cuts N (T := T) (fun j l hl => ?_)
      (fun j => mul_nonneg hθ.le (h0 j)) (fun t ht => ?_) fun t ht S htS => ?_).isAchievable
    · by_cases hj : j ∈ Src
      · simpa [hj] using hl
      · simp [hj] at hl
    · have : t ∉ Src := fun h => Finset.disjoint_left.mp hdisj h ht
      simp [hR t this]
    · have hsrc : ∑ j ∈ S, R j = ∑ j ∈ cutSources (fun j => if j ∈ Src then T else ∅) S, R j := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun j hj hjn => ?_).symm
        refine hR j fun hjS => hjn (Finset.mem_filter.mpr ⟨hj, t, ?_⟩)
        simp [hjS, ht, htS]
      have hb := hS S
      rw [← hsrc] at hb
      rw [← Finset.mul_sum]
      by_cases hz : ∑ j ∈ S, R j = 0
      · exact Or.inl (by simp [hz])
      · refine Or.inr (lt_of_lt_of_le ?_ hb)
        have hpos : 0 < ∑ j ∈ S, R j :=
          lt_of_le_of_ne (Finset.sum_nonneg fun j _ => h0 j) (Ne.symm hz)
        nlinarith
  exact mem_closure_of_forall_smul fun θ hθ hθ₁ => hach θ hθ hθ₁

end InfoTheory
