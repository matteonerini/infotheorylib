/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.SupportLemma
public import InfoTheoryLib.Network.DMNetwork

/-!
# Tools for cardinality bounds

The tools for bounding the cardinality of an auxiliary random variable, as in Appendix C of El Gamal
and Kim: the set of pmfs is connected, the entropy of an output is continuous in the input, and a
mixture of pmfs can be replaced by a mixture of few pmfs that preserves an output law and the means
of some continuous functions. With a bounded alphabet a region is a closed set.

## Main statements

* `isConnected_setOf_isPMF`: the set of pmfs is connected.
* `exists_mixture_preserving`: **the support lemma for pmfs**, with an output preserved.
* `continuousOn_condMutualInfo_jointOf`, `continuousOn_mutualInfo_jointOf`: informations are
  continuous in the input law.
* `isClosed_exists_forall_le`: a set of rates bounded by continuous functions on a compact set of
  laws is closed.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Appendix
  C
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α]

/-- The set of pmfs is convex. -/
lemma convex_setOf_isPMF : Convex ℝ {p : α → ℝ | IsPMF p} := by
  intro p hp p' hp' a b ha hb hab
  refine ⟨fun x => ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha (hp.nonneg x)) (mul_nonneg hb (hp'.nonneg x))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      hp.sum_eq_one, hp'.sum_eq_one, mul_one, hab]

/-- The set of pmfs is connected. -/
lemma isConnected_setOf_isPMF [Nonempty α] : IsConnected {p : α → ℝ | IsPMF p} :=
  ⟨⟨uniformPMF α, uniformPMF_isPMF⟩, convex_setOf_isPMF.isPreconnected⟩

/-- The output of a mean of inputs is the mean of the outputs. -/
lemma outDist_mean {ι : Type*} [Fintype ι] (a : ι → ℝ) (b : ι → α → ℝ) (T : α → β → ℝ) :
    outDist (∑ i, a i • b i) T = ∑ i, a i • outDist (b i) T := by
  funext y
  simp only [outDist, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun x _ => by ring

/-- The output of the output is the output of the composed channel. -/
lemma outDist_outDist {γ : Type*} [Fintype β] (t : α → ℝ) (T : α → β → ℝ) (V : β → γ → ℝ) :
    outDist (outDist t T) V = outDist t fun x y => ∑ b, T x b * V b y := by
  funext y
  simp only [outDist, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun b _ => by ring

/-- The entropy of the output is continuous in the input. -/
lemma continuous_entropy_outDist [Fintype β] (T : α → β → ℝ) :
    Continuous fun t : α → ℝ => entropy (outDist t T) := by
  simp only [entropy_eq_sum_negMulLog, outDist]
  exact continuous_finsetSum _ fun y _ => continuous_negMulLog.comp (by fun_prop)

/-- The mean output sums to one. -/
lemma sum_mean_outDist {ν A ι : Type*} [Fintype ν] [Fintype A] [Fintype ι] {L : ν → A → ℝ}
    (hL : IsChannel L) {c : ι → ℝ} {d : ι → ν → ℝ} (hc : IsPMF c) (hd : IsChannel d) :
    ∑ y, (∑ i, c i • outDist (d i) L) y = 1 := by
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [sum_comm]
  simp only [← mul_sum, (outDist_isPMF (hd _) hL).sum_eq_one, mul_one, hc.sum_eq_one]

/-- **The support lemma for pmfs.** A mixture of pmfs on `ν` with weights `a` can be replaced by a
mixture of `|A| - 1 + |κ|` pmfs that preserves the mean output of a channel `L : ν → A` and the
means of `|κ|` continuous functions. -/
theorem exists_mixture_preserving {ν A κ ι : Type*} [Fintype ν] [Fintype A] [Fintype κ] [Fintype ι]
    [Nonempty κ] [Nonempty ν] {L : ν → A → ℝ} (hL : IsChannel L) {f : κ → (ν → ℝ) → ℝ}
    (hf : ∀ k, ContinuousOn (f k) {p | IsPMF p}) {a : ι → ℝ} (ha : IsPMF a) {b : ι → ν → ℝ}
    (hb : IsChannel b) {n : ℕ} (hn : Fintype.card A - 1 + Fintype.card κ = n) :
    ∃ (w : Fin n → ℝ) (z : Fin n → ν → ℝ), IsPMF w ∧ IsChannel z ∧
      ∑ i, w i • outDist (z i) L = ∑ i, a i • outDist (b i) L ∧
        ∀ k, ∑ i, w i * f k (z i) = ∑ i, a i * f k (b i) := by
  classical
  obtain ⟨ν₀⟩ := ‹Nonempty ν›
  have hA : Nonempty A := by
    obtain ⟨y⟩ : Nonempty A := Fintype.card_pos_iff.1 (card_pos_of_isPMF (hL ν₀))
    exact ⟨y⟩
  obtain ⟨a₀⟩ := hA
  have hcard : Fintype.card ({y : A // y ≠ a₀} ⊕ κ) = n := by
    rw [Fintype.card_sum, ← hn]
    simp [Fintype.card_subtype_compl]
  subst hcard
  set g : {y : A // y ≠ a₀} ⊕ κ → (ν → ℝ) → ℝ :=
    Sum.elim (fun y t => outDist t L y) (fun k t => f k t) with hg
  have hgc : ∀ j, ContinuousOn (g j) {p | IsPMF p} := by
    rintro (y | k)
    · simp only [hg, Sum.elim_inl, outDist]
      exact Continuous.continuousOn (by fun_prop)
    · exact hf k
  have : Nonempty ({y : A // y ≠ a₀} ⊕ κ) := ⟨Sum.inr (Classical.arbitrary κ)⟩
  obtain ⟨w, z, hz, hw0, hw1, h⟩ := exists_fin_mixture_eq_sum (g := g)
    isConnected_setOf_isPMF hgc ha.nonneg ha.sum_eq_one (r := b) hb
  refine ⟨w, z, ⟨hw0, hw1⟩, hz, ?_, fun k => h (Sum.inr k)⟩
  have hne : ∀ y, y ≠ a₀ → (∑ i, w i • outDist (z i) L) y = (∑ i, a i • outDist (b i) L) y := by
    intro y hy
    have e := h (Sum.inl ⟨y, hy⟩)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg, Sum.elim_inl] using e
  funext y
  by_cases hy : y = a₀
  · subst hy
    have e1 := sum_mean_outDist hL (c := w) (d := z) ⟨hw0, hw1⟩ hz
    have e2 := sum_mean_outDist hL ha hb
    rw [← Finset.add_sum_erase _ _ (mem_univ y)] at e1 e2
    have e3 : ∑ y' ∈ univ.erase y, (∑ i, w i • outDist (z i) L) y' =
        ∑ y' ∈ univ.erase y, (∑ i, a i • outDist (b i) L) y' :=
      sum_congr rfl fun y' hy' => hne y' (ne_of_mem_erase hy')
    linarith
  · exact hne y hy

/-- A set of rates bounded by continuous functions on a compact set of laws is closed. -/
theorem isClosed_exists_forall_le {X E J : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {K : Set X} (hK : IsCompact K) {L : J → E → ℝ} (hL : ∀ j, Continuous (L j)) {F : J → X → ℝ}
    (hF : ∀ j, ContinuousOn (F j) K) : IsClosed {R | ∃ q ∈ K, ∀ j, L j R ≤ F j q} := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : IsClosed {z : K × E | ∀ j, L j z.2 ≤ F j z.1} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun j => isClosed_le ((hL j).comp continuous_snd) ?_
    exact (continuousOn_iff_continuous_domRestrict.1 (hF j)).comp continuous_fst
  have h := isClosedMap_snd_of_compactSpace _ hc
  convert h using 1
  ext R
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨(⟨q, hq⟩, R), h, rfl⟩
  · rintro ⟨⟨q, R'⟩, h, rfl⟩
    exact ⟨q, q.2, h⟩

section Continuity

variable {𝒵 γ a b c : Type*} [Fintype 𝒵] [Fintype γ] [Fintype a] [Fintype b] [Fintype c]

/-- A conditional mutual information is continuous in the input law. -/
lemma continuousOn_condMutualInfo_jointOf {K : 𝒵 → γ → ℝ} (hK : IsChannel K) (A : 𝒵 × γ → a)
    (B : 𝒵 × γ → b) (C : 𝒵 × γ → c) :
    ContinuousOn (fun q => I[A : B | C ; jointOf q K]) {q | IsPMF q} := by
  have hC : Continuous fun q : 𝒵 → ℝ =>
      H[pair C A ; jointOf q K] - H[C ; jointOf q K] -
        (H[pair (pair B C) A ; jointOf q K] - H[pair B C ; jointOf q K]) :=
    ((continuous_entropyRV_jointOf_input K _).sub (continuous_entropyRV_jointOf_input K _)).sub
      ((continuous_entropyRV_jointOf_input K _).sub (continuous_entropyRV_jointOf_input K _))
  refine hC.continuousOn.congr fun q hq => ?_
  have hμ := jointOf_isPMF hq hK
  rw [condMutualInfo, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]

/-- A mutual information is continuous in the input law. -/
lemma continuousOn_mutualInfo_jointOf {K : 𝒵 → γ → ℝ} (hK : IsChannel K) (A : 𝒵 × γ → a)
    (B : 𝒵 × γ → b) : ContinuousOn (fun q => I[A : B ; jointOf q K]) {q | IsPMF q} := by
  have hC : Continuous fun q : 𝒵 → ℝ =>
      H[B ; jointOf q K] - (H[pair A B ; jointOf q K] - H[A ; jointOf q K]) :=
    (continuous_entropyRV_jointOf_input K _).sub
      ((continuous_entropyRV_jointOf_input K _).sub (continuous_entropyRV_jointOf_input K _))
  refine hC.continuousOn.congr fun q hq => ?_
  have hμ := jointOf_isPMF hq hK
  rw [mutualInfo_eq_entropy_sub_condEntropy' hμ, condEntropy_eq_sub hμ]

end Continuity

end InfoTheory
