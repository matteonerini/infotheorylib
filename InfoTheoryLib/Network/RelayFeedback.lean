/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.RelayClasses

/-!
# The relay channel with feedback

Theorem 5 of Lecture 18: with feedback the capacity of the relay channel is the cutset bound.
Feedback from the receiver to the relay turns the relay channel into a degraded one, in which the
relay observes `(Y, Y₁)`.

## Main definitions

* `rcFBChannel W`: the relay channel in which the relay also observes `Y`.

## Main statements

* `isAchievableRCFB_of_lt`: every rate below the cutset bound is achievable with feedback.
* `rcfbCapacity_eq`: **Theorem 5**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {X X₁ Y Y₁ : Type*} [Fintype X] [Fintype X₁] [Fintype Y] [Fintype Y₁]
  {W : X × X₁ → Y × Y₁ → ℝ}

open Classical in
/-- The relay channel in which the relay observes `(Y, Y₁)`. -/
def rcFBChannel (W : X × X₁ → Y × Y₁ → ℝ) : X × X₁ → Y × (Y × Y₁) → ℝ :=
  fun a o => if o.1 = o.2.1 then W a o.2 else 0

omit [Fintype X] [Fintype X₁] in
/-- The channel is the pushforward of the original channel. -/
lemma rcFBChannel_eq (a : X × X₁) : rcFBChannel W a = dist (W a) fun o => (o.1, o) := by
  classical
  funext ⟨y, o⟩
  by_cases h : y = o.1
  · subst h
    have := dist_comp_of_injective (W a) id (f := fun o : Y × Y₁ => (o.1, o))
      (fun p q h => (Prod.ext_iff.mp h).2) o
    rw [dist_id] at this
    simpa [rcFBChannel] using this.symm
  · have h₀ : rcFBChannel W a (y, o) = 0 := by simp [rcFBChannel, h]
    rw [h₀]
    symm
    simp only [dist]
    refine sum_eq_zero fun p _ => ite_eq_right fun hp => ?_
    have h₁ : p.1 = y := (Prod.ext_iff.mp hp).1
    have h₂ : p = o := (Prod.ext_iff.mp hp).2
    exact h (h₁.symm.trans (congrArg Prod.fst h₂))

omit [Fintype X] [Fintype X₁] in
lemma rcFBChannel_isChannel (hW : IsChannel W) : IsChannel (rcFBChannel W) := fun a => by
  rw [rcFBChannel_eq]
  exact (hW a).dist _

/-- The joint law of the channel in which the relay observes `(Y, Y₁)`. -/
lemma jointOf_rcFBChannel (p : X × X₁ → ℝ) :
    jointOf p (rcFBChannel W) = dist (jointOf p W) fun z => (z.1, (z.2.1, z.2)) := by
  classical
  funext ⟨a, y, o⟩
  by_cases h : y = o.1
  · subst h
    have := dist_comp_of_injective (jointOf p W) id
      (f := fun z : (X × X₁) × (Y × Y₁) => (z.1, (z.2.1, z.2)))
      (fun u v h => Prod.ext (Prod.ext_iff.mp h).1 (Prod.ext_iff.mp (Prod.ext_iff.mp h).2).2) (a, o)
    rw [dist_id] at this
    refine Eq.trans ?_ this.symm
    simp [jointOf, rcFBChannel]
  · have h₀ : jointOf p (rcFBChannel W) (a, y, o) = 0 := by simp [jointOf, rcFBChannel, h]
    rw [h₀]
    symm
    simp only [dist]
    refine sum_eq_zero fun u _ => ite_eq_right fun hu => ?_
    have h₁ := (Prod.ext_iff.mp hu).2
    have h₂ : u.2.1 = y := (Prod.ext_iff.mp h₁).1
    have h₃ : u.2 = o := (Prod.ext_iff.mp h₁).2
    exact h (h₂.symm.trans (congrArg Prod.fst h₃))

omit [Fintype X] [Fintype X₁] in
/-- The marginal of `Y` does not change. -/
lemma bcMarg₁_rcFBChannel : bcMarg₁ (rcFBChannel W) = bcMarg₁ W := by
  classical
  funext a y
  simp only [bcMarg₁, rcFBChannel, Fintype.sum_prod_type]
  rw [sum_eq_single y]
  · simp
  · intro y' _ hy
    exact sum_eq_zero fun s _ => ite_eq_right fun h => hy h.symm
  · simp

/-- The two terms of decode–forward for the new channel are the two terms of the cutset bound. -/
lemma rcDfInfo_rcFBChannel {p : X × X₁ → ℝ} (hp : IsPMF p) (hW : IsChannel W) :
    rcDfInfo p (rcFBChannel W) = rcBcInfo p W := by
  have hJ := jointOf_isPMF hp hW
  simp only [rcDfInfo, rcBcInfo]
  rw [jointOf_rcFBChannel, condMutualInfo_dist hJ]
  rfl

section Code

variable {M n : ℕ}

/-- A code for the channel in which the relay observes `(Y, Y₁)` is a code with feedback. -/
def RCCode.ofFB (c : RCCode M n X X₁ Y (Y × Y₁)) : RCFBCode M n X X₁ Y Y₁ where
  enc k m _ := c.enc k m
  relay k z := c.relay k z
  dec := c.dec

/-- The map that copies the output `Y` to the relay. -/
def rcCopy {M k : ℕ} (t : Fin M × (Fin k → Y × Y₁)) : Fin M × (Fin k → Y × (Y × Y₁)) :=
  (t.1, fun i => ((t.2 i).1, t.2 i))

omit [Fintype Y] [Fintype Y₁] in
lemma rcCopy_injective {M k : ℕ} :
    Function.Injective (rcCopy (M := M) (k := k) (Y := Y) (Y₁ := Y₁)) :=
  fun _ _ h => Prod.ext (Prod.ext_iff.mp h).1 (funext fun i =>
    (Prod.ext_iff.mp (congrFun (Prod.ext_iff.mp h).2 i)).2)

omit [Fintype X] [Fintype X₁] in
/-- The law of the code for the new channel. -/
lemma law_ofFB (c : RCCode M n X X₁ Y (Y × Y₁)) (k : ℕ) :
    c.law (rcFBChannel W) k = dist (c.ofFB.law W k) rcCopy := by
  classical
  funext ⟨w, z'⟩
  by_cases h : ∀ i, (z' i).1 = (z' i).2.1
  · have hz : (w, z') = rcCopy (w, fun i => (z' i).2) := by
      refine Prod.ext rfl (funext fun i => Prod.ext (h i) rfl)
    rw [hz]
    have := dist_comp_of_injective (c.ofFB.law W k) id rcCopy_injective (w, fun i => (z' i).2)
    rw [dist_id] at this
    refine Eq.trans ?_ this.symm
    simp only [rcCopy, RCCode.law, RCFBCode.law]
    rw [fbLaw_eq_prod, fbLaw_eq_prod]
    congr 1
    refine prod_congr rfl fun i _ => ?_
    simp [rcFBChannel, RCCode.fbEnc, RCFBCode.fbEnc, RCCode.ofFB]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have h₀ : c.law (rcFBChannel W) k (w, z') = 0 := by
      rw [RCCode.law, fbLaw_eq_prod]
      refine mul_eq_zero_of_right _ (prod_eq_zero (mem_univ i) ?_)
      exact ite_eq_right hi
    rw [h₀]
    symm
    simp only [dist]
    refine sum_eq_zero fun t _ => ite_eq_right fun ht => ?_
    have h₂ : (rcCopy t).2 = z' := (Prod.ext_iff.mp ht).2
    subst h₂
    exact absurd rfl hi

omit [Fintype X] [Fintype X₁] in
/-- The code with feedback has the same probability of error. -/
lemma errProb_ofFB (c : RCCode M n X X₁ Y (Y × Y₁)) :
    c.ofFB.errProb W = c.errProb (rcFBChannel W) := by
  classical
  simp only [RCCode.errProb, RCFBCode.errProb, InfoTheory.errProb]
  rw [law_ofFB]
  have h := sum_dist_mul (c.ofFB.law W n) rcCopy fun a => if c.dec (fun i => (a.2 i).1) ≠ a.1 then
    (1 : ℝ) else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  convert h.symm using 3
  exact Iff.rfl

end Code

/-- **Page 18-44 of [elgamal2010].** Every rate below the cutset bound is achievable with feedback,
by decode–forward for the channel in which the relay observes `(Y, Y₁)`. Only the feedback from the
receiver to the relay is used. -/
theorem isAchievableRCFB_of_lt [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁]
    {p : X × X₁ → ℝ} (hp : IsPMF p) (hW : IsChannel W) {R : ℝ} (h₁ : R * log 2 < rcMacInfo p W)
    (h₂ : R * log 2 < rcBcInfo p W) : IsAchievableRCFB W R := by
  have hW' := rcFBChannel_isChannel hW
  have hmac : rcMacInfo p (rcFBChannel W) = rcMacInfo p W := by
    simp only [rcMacInfo, bcMarg₁_rcFBChannel]
  obtain ⟨c, hc⟩ := isAchievableRC_decodeForward hp hW' (by rwa [hmac])
    (by rwa [rcDfInfo_rcFBChannel hp hW])
  refine ⟨fun n => (c n).ofFB, ?_⟩
  simp_rw [errProb_ofFB]
  exact hc

/-- **Theorem 5 of Lecture 18 of [elgamal2010], page 18-44.** The capacity of the relay channel with
feedback is `max_{p(x, x₁)} min {I(X, X₁; Y), I(X; Y, Y₁ | X₁)}`. -/
theorem rcfbCapacity_eq [Nonempty X] [Nonempty X₁] [Nonempty Y] [Nonempty Y₁] (hW : IsChannel W) :
    rcfbCapacity W = rcCutsetBound W / log 2 := by
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have h₁ : ∀ R, R * log 2 < rcCutsetBound W → IsAchievableRCFB W R := by
    intro R hR
    have hne : {v | ∃ p : X × X₁ → ℝ, IsPMF p ∧ v = min (rcMacInfo p W) (rcBcInfo p W)}.Nonempty :=
      ⟨_, uniformPMF _, uniformPMF_isPMF, rfl⟩
    obtain ⟨_, ⟨p, hp, rfl⟩, hv⟩ := exists_lt_of_lt_csSup hne hR
    exact isAchievableRCFB_of_lt hp hW (hv.trans_le (min_le_left _ _))
      (hv.trans_le (min_le_right _ _))
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨0, (isAchievableRC_of_nonpos le_rfl).toFB⟩
    (fun R hR => (le_div_iff₀ hlog2).mpr (hR.le_rcCutsetBound hW)) fun a ha => ?_
  obtain ⟨b, hab, hb⟩ := exists_between ha
  exact ⟨b, h₁ b ((lt_div_iff₀ hlog2).mp hb), hab⟩

end InfoTheory
