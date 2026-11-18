/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.SideInfoConverse

/-!
# Source coding with side information: the simple special cases

This file treats the special cases of Lecture 12 in which the side information is available at the
encoder. Each of them reduces to another theorem, with no new coding argument.

* **At the encoder only**, the side information does not help: `R_SI-E(D) = R(D)`. For each `xⁿ`,
  the encoder can use the best `yⁿ`, which gives a code without side information of no larger
  distortion.
* **At both the encoder and the decoder**, `R_SI-ED(D) = min_{p(x̂ | x, y)} I(X; X̂ | Y)`. The notes
  say that this is easy to show. A code is a Wyner–Ziv code for the source `(X, Y)` with side
  information `Y`, and the formula follows from the Wyner–Ziv theorem.

We also prove `R_SI-ED(D) ≤ R_SI-D(D) ≤ R_CSI-D(D) ≤ R(D)`.

## Main definitions

* `EncSideCode`, `IsAchievableEncSideBits`, `rateEncSideBits`: side information at the encoder only.
* `BothSideCode`, `IsAchievableBothBits`, `rateBothBits`: side information at both ends.
* `bothLaw P q`: the law `p(x, y) p(x̂ | x, y)`.
* `bothRD P d D`: `min I(X; X̂ | Y)`, in nats.

## Main statements

* `rateEncSideBits_eq`: `R_SI-E(D) = R(D)`.
* `rateBothBits_eq`: `R_SI-ED(D) = min I(X; X̂ | Y)`.
* `bothRD_hamming_zero`: `R_SI-ED(0) = H(X | Y)` for the Hamming distortion.
* `bothRD_le_wzRD`, `wzRD_le_causalRD`, `causalRD_le_infoRD`: the inequalities on page 12-17.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 12
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α γ β υ : Type*} [Fintype α] [Fintype γ] {P : α × γ → ℝ} {d : α → β → ℝ}

/-! ### Side information at the encoder only -/

section Encoder

/-- **Lecture 12 of [elgamal2010], page 12-3.** A code with side information at the encoder only. -/
structure EncSideCode (M n : ℕ) (α γ β : Type*) where
  /-- The encoder. -/
  enc : (Fin n → α) → (Fin n → γ) → Fin M
  /-- The decoder. -/
  dec : Fin M → Fin n → β

/-- The expected distortion of a code with side information at the encoder only. -/
def EncSideCode.distortion {M n : ℕ} (c : EncSideCode M n α γ β) (P : α × γ → ℝ) (d : α → β → ℝ) :
    ℝ :=
  ∑ ω, iidPMF P n ω * seqDistortion d (fstSeq ω) (c.dec (c.enc (fstSeq ω) (sndSeq ω)))

/-- **Lecture 12 of [elgamal2010], page 12-3.** A pair `(R, D)`, with `R` in bits, is achievable
with side information at the encoder only. -/
def IsAchievableEncSideBits (P : α × γ → ℝ) (d : α → β → ℝ) (R D : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, EncSideCode (2 ^ ⌊n * R⌋₊) n α γ β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion P d ≤ D + ε

/-- **Lecture 12 of [elgamal2010], page 12-3.** The rate–distortion function `R_SI-E(D)`, in bits.
-/
def rateEncSideBits (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | IsAchievableEncSideBits P d R D}

/-- For each `xⁿ` the best `yⁿ` gives a code without side information of no larger distortion. -/
lemma EncSideCode.exists_rdCode_le (hP : IsPMF P) {M n : ℕ} (c : EncSideCode M n α γ β) :
    ∃ c' : RDCode M n α β, c'.distortion (margFst P) d ≤ c.distortion P d := by
  classical
  obtain ⟨W, hW, hPW⟩ := exists_side_channel hP
  obtain ⟨z⟩ : Nonempty (α × γ) := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hne : Nonempty (Fin n → γ) := ⟨fun _ => z.2⟩
  choose y hy using fun x : Fin n → α => Finite.exists_min fun y =>
    seqDistortion d x (c.dec (c.enc x y))
  refine ⟨⟨fun x => c.enc x (y x), c.dec⟩, ?_⟩
  simp only [RDCode.distortion, EncSideCode.distortion]
  rw [← sum_jointIid P n fun ω => seqDistortion d (fstSeq ω) (c.dec (c.enc (fstSeq ω) (sndSeq ω))),
    Fintype.sum_prod_type]
  refine sum_le_sum fun x _ => ?_
  have hs : ∑ y', jointIid P n (x, y') * seqDistortion d x (c.dec (c.enc x y')) =
      iidPMF (margFst P) n x * ∑ y', channelExt W n x y' *
        seqDistortion d x (c.dec (c.enc x y')) := by
    rw [mul_sum]
    refine sum_congr rfl fun y' _ => ?_
    change iidPMF P n (zipSeq x y') * _ = _
    rw [iidPMF_zip_eq hPW]
    ring
  refine le_of_le_of_eq ?_ hs.symm
  refine mul_le_mul_of_nonneg_left ?_ (iidPMF_nonneg (hP.dist _).nonneg x)
  calc seqDistortion d x (c.dec (c.enc x (y x)))
      = ∑ y', channelExt W n x y' * seqDistortion d x (c.dec (c.enc x (y x))) := by
        rw [← sum_mul, ((hW.ext n) x).sum_eq_one, one_mul]
    _ ≤ _ := sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left (hy x y')
        (channelExt_nonneg hW x y')

/-- **Lecture 12 of [elgamal2010], page 12-3.** Side information available only at the encoder does
not help: `R_SI-E(D) = R(D)`, for `D ≥ D_min`, in bits. -/
theorem rateEncSideBits_eq [Fintype β] [Nonempty β] (hP : IsPMF P) (hd : ∀ x y, 0 ≤ d x y) {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) :
    rateEncSideBits P d D = infoRD (margFst P) d D / log 2 := by
  have hp : IsPMF (margFst P) := hP.dist _
  have hach : ∀ R, infoRD (margFst P) d D / log 2 < R → IsAchievableEncSideBits P d R D :=
    fun R hR => by
      obtain ⟨hR0, c, hc⟩ := isAchievableRDBits_of_lt hp hd hD hR
      refine ⟨hR0, fun n => ⟨fun x _ => (c n).enc x, (c n).dec⟩, fun ε hε => ?_⟩
      filter_upwards [hc ε hε] with n hn
      refine le_of_eq_of_le ?_ hn
      simp only [EncSideCode.distortion, RDCode.distortion]
      rw [← sum_jointIid P n fun ω => seqDistortion d (fstSeq ω) ((c n).dec ((c n).enc (fstSeq ω)))]
      exact sum_jointIid_fst P n fun x => seqDistortion d x ((c n).dec ((c n).enc x))
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ⟨_, hach _ (lt_add_one _)⟩ (fun R hR => ?_)
    fun w hw => ⟨(infoRD (margFst P) d D / log 2 + w) / 2, hach _ (by linarith), by linarith⟩
  obtain ⟨hR0, c, hc⟩ := hR
  refine IsAchievableRDBits.infoRD_div_le hp (d := d) ⟨hR0, ?_⟩
  choose c' hc' using fun n => (c n).exists_rdCode_le (d := d) hP
  exact ⟨c', fun ε hε => (hc ε hε).mono fun n hn => (hc' n).trans hn⟩

end Encoder

/-! ### Side information at both the encoder and the decoder -/

section Both

variable [Fintype υ]

/-- **Lecture 12 of [elgamal2010], page 12-3.** A code with side information at the encoder and the
decoder. -/
structure BothSideCode (M n : ℕ) (α γ β : Type*) where
  /-- The encoder. -/
  enc : (Fin n → α) → (Fin n → γ) → Fin M
  /-- The decoder. -/
  dec : Fin M → (Fin n → γ) → Fin n → β

/-- The expected distortion of a code with side information at both ends. -/
def BothSideCode.distortion {M n : ℕ} (c : BothSideCode M n α γ β) (P : α × γ → ℝ) (d : α → β → ℝ) :
    ℝ :=
  ∑ ω, iidPMF P n ω * seqDistortion d (fstSeq ω) (c.dec (c.enc (fstSeq ω) (sndSeq ω)) (sndSeq ω))

/-- **Lecture 12 of [elgamal2010], page 12-3.** A pair `(R, D)`, with `R` in bits, is achievable
with side information at both ends. -/
def IsAchievableBothBits (P : α × γ → ℝ) (d : α → β → ℝ) (R D : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, BothSideCode (2 ^ ⌊n * R⌋₊) n α γ β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion P d ≤ D + ε

/-- **Lecture 12 of [elgamal2010], page 12-3.** The rate–distortion function `R_SI-ED(D)`, in bits.
-/
def rateBothBits (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | IsAchievableBothBits P d R D}

/-- The law `p(x, y) p(u | x, y)` of `((X, Y), U)`. -/
abbrev bothLaw (P : α × γ → ℝ) (q : α × γ → υ → ℝ) : (α × γ) × υ → ℝ := jointOf P q

/-- `I(X; U | Y)` under the law `p(x, y) p(u | x, y)`, in nats. -/
def bothRate (P : α × γ → ℝ) (q : α × γ → υ → ℝ) : ℝ :=
  I[fun z : (α × γ) × υ => z.1.1 : Prod.snd | fun z => z.1.2 ; bothLaw P q]

/-- **Lecture 12 of [elgamal2010], page 12-3.** `R_SI-ED(D) = min I(X; X̂ | Y)` over `p(x̂ | x, y)`
with `E d(X, X̂) ≤ D`, in nats. -/
def bothRD [Fintype β] (P : α × γ → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {I | ∃ q : α × γ → β → ℝ, IsChannel q ∧
    ∑ z, bothLaw P q z * d z.1.1 z.2 ≤ D ∧ bothRate P q = I}

/-- The source `(X, Y)` with side information `Y`. -/
def bothSource (P : α × γ → ℝ) : (α × γ) × γ → ℝ := dist P fun a => (a, a.2)

/-- The distortion measure of the source `(X, Y)`. -/
def bothDist (d : α → β → ℝ) (a : α × γ) (b : β) : ℝ := d a.1 b

lemma bothSource_isPMF (hP : IsPMF P) : IsPMF (bothSource P) := hP.dist _

lemma margFst_bothSource : margFst (bothSource P) = P := by
  have h := dist_comp_eq P (fun a : α × γ => (a, a.2)) Prod.fst
  rw [show (Prod.fst ∘ fun a : α × γ => (a, a.2)) = id from rfl, dist_id] at h
  exact h.symm

/-- The sums for the source `(X, Y)` are sums for the source `P`. -/
lemma sum_iidPMF_bothSource {n : ℕ} (F : (Fin n → (α × γ) × γ) → ℝ) :
    ∑ ω', iidPMF (bothSource P) n ω' * F ω' =
      ∑ ω, iidPMF P n ω * F fun i => (ω i, (ω i).2) := by
  have h := dist_iidPMF_comp P n fun a => (a, a.2)
  have h2 := sum_dist_mul (iidPMF P n) (fun ω i => (ω i, (ω i).2)) F
  rw [h] at h2
  exact h2

/-- A code with side information at both ends is a Wyner–Ziv code for the source `(X, Y)`. -/
theorem isAchievableBothBits_iff {R D : ℝ} :
    IsAchievableBothBits P d R D ↔ IsAchievableWZBits (bothSource P) (bothDist d) R D := by
  have hdist : ∀ {M n : ℕ} (c : BothSideCode M n α γ β), (WZCode.mk
      (fun a => c.enc (fstSeq a) (sndSeq a)) c.dec).distortion (bothSource P) (bothDist d) =
      c.distortion P d := fun c => by
    simp only [WZCode.distortion, BothSideCode.distortion, sum_iidPMF_bothSource]
    rfl
  have hdist' : ∀ {M n : ℕ} (c : WZCode M n (α × γ) γ β), c.distortion (bothSource P) (bothDist d) =
      (BothSideCode.mk (fun x y => c.enc (zipSeq x y)) c.dec).distortion P d := fun c => by
    simp only [WZCode.distortion, BothSideCode.distortion, sum_iidPMF_bothSource]
    rfl
  constructor
  · rintro ⟨hR, c, hc⟩
    refine ⟨hR, fun n => ⟨fun a => (c n).enc (fstSeq a) (sndSeq a), (c n).dec⟩, fun ε hε => ?_⟩
    filter_upwards [hc ε hε] with n hn
    rwa [hdist]
  · rintro ⟨hR, c, hc⟩
    refine ⟨hR, fun n => ⟨fun x y => (c n).enc (zipSeq x y), (c n).dec⟩, fun ε hε => ?_⟩
    filter_upwards [hc ε hε] with n hn
    rwa [← hdist']

/-- The law of `((X, Y), Y, U)` under the source `(X, Y)`. -/
lemma siLaw_bothSource (q : α × γ → υ → ℝ) :
    siLaw (bothSource P) q = dist (bothLaw P q) fun z => ((z.1, z.1.2), z.2) := by
  classical
  have hinj : Function.Injective fun z : (α × γ) × υ => ((z.1, z.1.2), z.2) := by
    rintro ⟨a, u⟩ ⟨a', u'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 h.2
  funext ⟨⟨a, y⟩, u⟩
  simp only [siLaw, jointOf, bothLaw]
  by_cases hy : a.2 = y
  · subst hy
    have h1 : bothSource P (a, a.2) = P a := by
      have h := dist_comp_of_injective P id (f := fun a : α × γ => (a, a.2))
        (fun x x' h => (Prod.mk.inj h).1) a
      rw [dist_id] at h
      exact h
    have h2 := dist_comp_of_injective (jointOf P q) id hinj (a, u)
    rw [dist_id] at h2
    rw [h1]
    exact h2.symm
  · have h1 : bothSource P (a, y) = 0 := by
      refine dist_eq_zero_of_forall_ne _ fun b hb => hy ?_
      have := Prod.mk.inj hb
      rw [← this.1]
      exact this.2
    rw [h1, zero_mul]
    refine (dist_eq_zero_of_forall_ne _ fun z hz => hy ?_).symm
    have := Prod.mk.inj (Prod.mk.inj hz).1
    rw [← this.1]
    exact this.2

/-- `H(f(C), X | C) = H(X | C)`. -/
lemma condEntropy_pair_comp {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → a) (C : Ω → c) (f : c → b) :
    H[fun ω => (X ω, f (C ω)) | C ; μ] = H[X | C ; μ] := by
  rw [condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  congr 1
  refine entropyRV_eq_of_injective μ (fun w : c × a => (w.1, (w.2, f w.1))) ?_ fun _ => rfl
  rintro ⟨c₁, a₁⟩ ⟨c₂, a₂⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

variable {q : α × γ → υ → ℝ}

/-- `I(X, Y; U | Y) = I(X; U | Y)`: the Wyner–Ziv rate of the source `(X, Y)` is `I(X; U | Y)`. -/
theorem sideRate_bothSource (hP : IsPMF P) (hq : IsChannel q) :
    sideRate 1 (bothSource P) q = bothRate P q := by
  classical
  have hμ : IsPMF (bothLaw P q) := jointOf_isPMF hP hq
  have hμ' := siLaw_isPMF (bothSource_isPMF hP) hq
  rw [sideRate_one (bothSource_isPMF hP) hq, condMutualInfo, bothRate, condMutualInfo]
  have e1 : H[fun z : ((α × γ) × γ) × υ => z.1.1 | fun z => z.1.2 ; siLaw (bothSource P) q] =
      H[fun z : (α × γ) × υ => z.1 | fun z => z.1.2 ; bothLaw P q] := by
    refine condEntropy_eq_of_dist_pair_eq hμ' hμ ?_
    rw [siLaw_bothSource, ← dist_comp_eq]
    rfl
  have e2 : H[fun z : ((α × γ) × γ) × υ => z.1.1 | pair Prod.snd (fun z => z.1.2) ;
      siLaw (bothSource P) q] =
      H[fun z : (α × γ) × υ => z.1 | pair Prod.snd (fun z => z.1.2) ; bothLaw P q] := by
    refine condEntropy_eq_of_dist_pair_eq hμ' hμ ?_
    rw [siLaw_bothSource, ← dist_comp_eq]
    rfl
  rw [e1, e2]
  congr 1
  · exact condEntropy_pair_comp hμ (fun z : (α × γ) × υ => z.1.1) (fun z => z.1.2) id
  · exact condEntropy_pair_comp hμ (fun z : (α × γ) × υ => z.1.1)
      (pair Prod.snd fun z => z.1.2) Prod.snd

/-- The kernel of `X̂ = x̂(U, Y)`. -/
def processKernel (q : α × γ → υ → ℝ) (f : υ → γ → β) (a : α × γ) (b : β) : ℝ :=
  open Classical in ∑ u, q a u * if f u a.2 = b then 1 else 0

omit [Fintype α] [Fintype γ] in
lemma processKernel_isChannel [Fintype β] (hq : IsChannel q) (f : υ → γ → β) :
    IsChannel (processKernel q f) := fun a => by
  classical
  refine ⟨fun b => sum_nonneg fun u _ => mul_nonneg ((hq a).nonneg u) (by split_ifs <;> norm_num),
    ?_⟩
  simp only [processKernel]
  rw [sum_comm]
  simp only [← mul_sum, Finset.sum_ite_eq, mem_univ, ite_true, mul_one, (hq a).sum_eq_one]

/-- The law of `((X, Y), X̂)`, for `X̂ = x̂(U, Y)`. -/
lemma bothLaw_process (f : υ → γ → β) :
    bothLaw P (processKernel q f) = dist (bothLaw P q) fun z => (z.1, f z.2 z.1.2) := by
  classical
  funext ⟨a, b⟩
  simp only [jointOf, processKernel, dist, Prod.mk.injEq, mul_sum]
  rw [Fintype.sum_prod_type, sum_eq_single a]
  · refine sum_congr rfl fun u _ => ?_
    by_cases h : f u a.2 = b <;> simp [h]
  · intro a' _ ha
    exact sum_eq_zero fun u _ => by simp [ha]
  · simp

/-- **Data processing.** `I(X; X̂ | Y) ≤ I(X; U | Y)`, for `X̂ = x̂(U, Y)`. -/
theorem bothRate_process_le [Fintype β] (hP : IsPMF P) (hq : IsChannel q) (f : υ → γ → β) :
    bothRate P (processKernel q f) ≤ bothRate P q := by
  classical
  have hμ : IsPMF (bothLaw P q) := jointOf_isPMF hP hq
  have hq' := processKernel_isChannel hq f
  have hμ' : IsPMF (bothLaw P (processKernel q f)) := jointOf_isPMF hP hq'
  have e1 : H[fun z : (α × γ) × β => z.1.1 | fun z => z.1.2 ; bothLaw P (processKernel q f)] =
      H[fun z : (α × γ) × υ => z.1.1 | fun z => z.1.2 ; bothLaw P q] := by
    refine condEntropy_eq_of_dist_pair_eq hμ' hμ ?_
    rw [bothLaw_process, ← dist_comp_eq]
    rfl
  have e2 : H[fun z : (α × γ) × β => z.1.1 | pair Prod.snd (fun z => z.1.2) ;
      bothLaw P (processKernel q f)] =
      H[fun z : (α × γ) × υ => z.1.1 | fun z => (f z.2 z.1.2, z.1.2) ; bothLaw P q] := by
    refine condEntropy_eq_of_dist_pair_eq hμ' hμ ?_
    rw [bothLaw_process, ← dist_comp_eq]
    rfl
  rw [bothRate, bothRate, condMutualInfo, condMutualInfo, e1, e2]
  have h := condEntropy_le_condEntropy_comp hμ (fun z : (α × γ) × υ => z.1.1)
    (pair Prod.snd fun z => z.1.2) fun w => (f w.1 w.2, w.2)
  have e3 : (fun w : υ × γ => (f w.1 w.2, w.2)) ∘
      pair (Prod.snd : (α × γ) × υ → υ) (fun z => z.1.2) = fun z => (f z.2 z.1.2, z.1.2) := rfl
  rw [e3] at h
  linarith

/-- The expected distortion of `X̂ = x̂(U, Y)`. -/
lemma sum_bothLaw_process [Fintype β] (f : υ → γ → β) (d : α → β → ℝ) :
    ∑ z, bothLaw P (processKernel q f) z * d z.1.1 z.2 =
      ∑ z, bothLaw P q z * d z.1.1 (f z.2 z.1.2) := by
  rw [bothLaw_process]
  exact sum_dist_mul (bothLaw P q) (fun z => (z.1, f z.2 z.1.2)) fun z => d z.1.1 z.2

/-- The cost for the source `(X, Y)`. -/
lemma sideCost_bothSource (c : υ → α × γ → γ → ℝ) :
    sideCost (bothSource P) q c = ∑ z, bothLaw P q z * c z.2 z.1 z.1.2 := by
  rw [sideCost, siLaw_bothSource]
  exact sum_dist_mul (bothLaw P q) (fun z => ((z.1, z.1.2), z.2)) fun z => c z.2 z.1.1 z.1.2

lemma bothRD_set_bddBelow [Fintype β] (hP : IsPMF P) (d : α → β → ℝ) (D : ℝ) :
    BddBelow {I | ∃ q : α × γ → β → ℝ, IsChannel q ∧
      ∑ z, bothLaw P q z * d z.1.1 z.2 ≤ D ∧ bothRate P q = I} :=
  ⟨0, by
    rintro _ ⟨q, hq, -, rfl⟩
    exact condMutualInfo_nonneg (jointOf_isPMF hP hq) _ _ _⟩

/-- `D_min` of the source `(X, Y)` is `D_min` of the source `X`. -/
lemma minDistortion_bothSource (P : α × γ → ℝ) (d : α → β → ℝ) :
    minDistortion (margFst (bothSource P)) (bothDist d) = minDistortion (margFst P) d := by
  rw [margFst_bothSource, minDistortion, minDistortion, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [margFst_apply, sum_mul]
  rfl

/-- **Lecture 12, page 12-17.** `R_SI-ED` is the Wyner–Ziv rate–distortion function of the source
`(X, Y)` with side information `Y`. -/
theorem bothRD_eq_wzRD [Fintype β] [Nonempty β] (hP : IsPMF P) {d : α → β → ℝ} {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) :
    bothRD P d D = wzRD (bothSource P) (bothDist d) D := by
  classical
  have hP' := bothSource_isPMF hP
  have hD' : minDistortion (margFst (bothSource P)) (bothDist d) ≤ D := by
    rwa [minDistortion_bothSource]
  obtain ⟨q₀, f₀, hq₀, hc₀, he₀⟩ := exists_sideRD_eq (θ := 1) hP' hD'
  have hc₀' : ∑ z, bothLaw P q₀ z * d z.1.1 (f₀ z.2 z.1.2) ≤ D := by
    have := sideCost_bothSource (P := P) (q := q₀) fun u a y => d a.1 (f₀ u y)
    rw [← this]
    exact hc₀
  refine le_antisymm ?_ ?_
  · refine (csInf_le (bothRD_set_bddBelow hP d D)
      ⟨processKernel q₀ f₀, processKernel_isChannel hq₀ f₀, ?_, rfl⟩).trans ?_
    · rw [sum_bothLaw_process]
      exact hc₀'
    · refine (bothRate_process_le hP hq₀ f₀).trans ?_
      rw [← sideRate_bothSource hP hq₀, he₀]
      rfl
  · refine le_csInf ⟨_, processKernel q₀ f₀, processKernel_isChannel hq₀ f₀,
      by rw [sum_bothLaw_process]; exact hc₀', rfl⟩ ?_
    rintro _ ⟨q, hq, hc, rfl⟩
    rw [← sideRate_bothSource hP hq]
    refine sideRD_le hP' hq 1 (fun u _ => u) ?_
    have := sideCost_bothSource (P := P) (q := q) fun u a _ => d a.1 u
    exact this.trans_le hc

/-- **Lecture 12 of [elgamal2010], page 12-3.** The rate–distortion function with side information
at both the encoder and the decoder is `R_SI-ED(D) = min I(X; X̂ | Y)`, over `p(x̂ | x, y)` with
`E d(X, X̂) ≤ D`, for `D ≥ D_min`, in bits. -/
theorem rateBothBits_eq [Fintype β] [Nonempty β] (hP : IsPMF P) {d : α → β → ℝ}
    (hd : ∀ x y, 0 ≤ d x y) {D : ℝ} (hD : minDistortion (margFst P) d ≤ D) :
    rateBothBits P d D = bothRD P d D / log 2 := by
  have e : {R | IsAchievableBothBits P d R D} =
      {R | IsAchievableWZBits (bothSource P) (bothDist d) R D} := by
    ext R
    exact isAchievableBothBits_iff
  rw [rateBothBits, e, bothRD_eq_wzRD hP hD]
  exact rateWZBits_eq (d := bothDist d) (bothSource_isPMF hP) (fun a b => hd a.1 b)
    (by rwa [minDistortion_bothSource])

/-! ### The lossless cases -/

open Classical in
/-- **Lecture 12, page 12-3.** For the Hamming distortion, `R_SI-ED(0) = H(X | Y)`. -/
theorem bothRD_hamming_zero (hP : IsPMF P) :
    bothRD P (hammingDistortion (α := α)) 0 = H[Prod.fst | Prod.snd ; P] := by
  have hval : ∀ q : α × γ → α → ℝ, IsChannel q →
      ∑ z, bothLaw P q z * hammingDistortion z.1.1 z.2 ≤ 0 →
        bothRate P q = H[Prod.fst | Prod.snd ; P] := fun q hq hc => by
    have hμ : IsPMF (bothLaw P q) := jointOf_isPMF hP hq
    have hnn : ∀ z ∈ univ, 0 ≤ bothLaw P q z * hammingDistortion z.1.1 z.2 := fun z _ =>
      mul_nonneg (hμ.nonneg z) (hammingDistortion_nonneg _ _)
    have h0 := (sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hc (sum_nonneg hnn))
    have hz : H[fun z : (α × γ) × α => z.1.1 | pair Prod.snd (fun z => z.1.2) ;
        bothLaw P q] = 0 := by
      refine (condEntropy_eq_zero_iff hμ _ _).2 ⟨Prod.fst, fun z hne => ?_⟩
      have hd := (mul_eq_zero.1 (h0 z (mem_univ z))).resolve_left hne
      by_contra hxy
      have h3 : z.1.1 ≠ z.2 := hxy
      simp [hammingDistortion, h3] at hd
    rw [bothRate, condMutualInfo, hz, sub_zero]
    refine condEntropy_eq_of_dist_pair_eq hμ hP ?_
    rw [show pair (fun z : (α × γ) × α => z.1.2) (fun z => z.1.1) =
      (pair Prod.snd Prod.fst) ∘ Prod.fst from rfl, dist_comp_eq, dist_jointOf_fst hq]
  have hid : IsChannel fun (a : α × γ) (b : α) => if b = a.1 then (1 : ℝ) else 0 := fun a => by
    refine ⟨fun b => by dsimp only; split_ifs <;> norm_num, ?_⟩
    simp
  have hc : ∑ z, bothLaw P (fun (a : α × γ) (b : α) => if b = a.1 then (1 : ℝ) else 0) z *
      hammingDistortion z.1.1 z.2 ≤ 0 := by
    refine le_of_eq (sum_eq_zero fun z _ => ?_)
    by_cases h : z.2 = z.1.1
    · simp [hammingDistortion, h]
    · simp [jointOf, h]
  have hset : {I | ∃ q : α × γ → α → ℝ, IsChannel q ∧
      ∑ z, bothLaw P q z * hammingDistortion z.1.1 z.2 ≤ 0 ∧ bothRate P q = I} =
      {H[Prod.fst | Prod.snd ; P]} := by
    ext I
    constructor
    · rintro ⟨q, hq, hc', rfl⟩
      exact hval q hq hc'
    · rintro rfl
      exact ⟨_, hid, hc, hval _ hid hc⟩
  rw [bothRD, hset, csInf_singleton]

/-! ### The inequalities between the rate–distortion functions -/

/-- **Lecture 12, page 12-17.** `R_SI-ED(D) ≤ R_SI-D(D)`. -/
theorem bothRD_le_wzRD [Fintype β] [Nonempty β] (hP : IsPMF P) {d : α → β → ℝ} {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) : bothRD P d D ≤ wzRD P d D := by
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 1) hP hD
  have hql : IsChannel fun a : α × γ => q a.1 := fun a => hq a.1
  refine (csInf_le (bothRD_set_bddBelow hP d D)
    ⟨processKernel _ f, processKernel_isChannel hql f, ?_, rfl⟩).trans
      ((bothRate_process_le hP hql f).trans (le_of_eq ?_))
  · rw [sum_bothLaw_process]
    exact hc
  · rw [wzRD, ← he, sideRate_one hP hq]
    rfl

/-- **Lecture 12, page 12-17.** `R_SI-D(D) ≤ R_CSI-D(D)`. -/
theorem wzRD_le_causalRD [Finite β] [Nonempty β] (hP : IsPMF P) {d : α → β → ℝ} {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) : wzRD P d D ≤ causalRD P d D := by
  obtain ⟨q, f, hq, hc, he⟩ := exists_sideRD_eq (θ := 0) hP hD
  refine (sideRD_le hP hq 1 f hc).trans ?_
  rw [causalRD, ← he, sideRate, sideRate]
  have := mutualInfo_nonneg (siLaw_isPMF hP hq) (fun z : (α × γ) × _ => z.1.2) Prod.snd
  linarith

/-- **Lecture 12, page 12-17.** `R_CSI-D(D) ≤ R(D)`. -/
theorem causalRD_le_infoRD [Fintype β] [Nonempty β] (hP : IsPMF P) {d : α → β → ℝ} {D : ℝ}
    (hD : minDistortion (margFst P) d ≤ D) : causalRD P d D ≤ infoRD (margFst P) d D := by
  obtain ⟨q, hq, hc, he⟩ := exists_infoRD_eq (hP.dist Prod.fst) hD
  have hcost : sideCost P q (fun u x _ => d x u) ≤ D := by
    rw [sideCost_test]
    exact hc
  refine (sideRD_le hP hq 0 (fun u _ => u) hcost).trans (le_of_eq ?_)
  rw [← he, sideRate, zero_mul, sub_zero, mutualInfoOf_side]

end Both

end InfoTheory
