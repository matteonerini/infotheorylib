/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.DMNetwork
public import InfoTheoryLib.Probability.SupportMixture

/-!
# Tools for cardinality bounds

The tools for bounding the cardinality of an auxiliary random variable, as in Appendix C of El Gamal
and Kim, beyond those of `Probability.SupportMixture`: informations are continuous in the input law,
and with a bounded alphabet a region is a closed set.

## Main statements

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
