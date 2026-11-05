/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Binary
public import InfoTheoryLib.RateDistortion.Theorem

/-!
# The lossy source coding theorem with rates in bits

El Gamal and Kim's lecture notes define a `(2^{nR}, n)` rate–distortion code with index set
`[1 : 2^{nR}) = {1, …, 2^⌊nR⌋}` and a rate `R` in bits; a pair `(R, D)` is achievable if there are
such codes with `limsup E d(Xⁿ, X̂ⁿ) ≤ D`, and the rate–distortion function `R(D)` is the infimum
of the rates `R` such that `(R, D)` is achievable. Cover and Thomas use `⌊e^{nR}⌋` indices with `R`
in nats, and define `R(D)` through the closure of the achievable region. We derive the lossy
source coding theorem for the definitions of the notes from `RateDistortion.Theorem`: a code can
always be given more indices without changing its distortion, so achievable rates transfer in both
directions.

We also show that the rate–distortion function at `D = 0` for the Hamming distortion is the
entropy, `R(0) = H(X)`: lossless source coding is a special case of lossy source coding.

## Main definitions

* `RDCode.castLE`: a rate–distortion code with more indices.
* `IsAchievableRDBits p d R D`: the pair `(R, D)` is achievable, with `R` in bits.
* `rateDistortionBits p d D`: the rate–distortion function `R(D)`, in bits.

## Main statements

* `rateDistortionBits_eq`: **the lossy source coding theorem**,
  `R(D) = min_{p(x̂|x) : E d(X, X̂) ≤ D} I(X; X̂)` for `D ≥ D_min`.
* `infoRD_hammingDistortion_zero`: `R(0) = H(X)` for the Hamming distortion.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 3
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {α β : Type*} [Fintype α] [Fintype β] {p : α → ℝ} {d : α → β → ℝ}

/-- A rate–distortion code with `M` indices used as a code with `M' ≥ M` indices. -/
def RDCode.castLE {M M' n : ℕ} (h : M ≤ M') (hM : 0 < M) (c : RDCode M n α β) :
    RDCode M' n α β where
  enc x := Fin.castLE h (c.enc x)
  dec m := if hm : (m : ℕ) < M then c.dec ⟨m, hm⟩ else c.dec ⟨0, hM⟩

omit [Fintype β] in
lemma RDCode.distortion_castLE {M M' n : ℕ} (h : M ≤ M') (hM : 0 < M) (c : RDCode M n α β) :
    (c.castLE h hM).distortion p d = c.distortion p d := by
  unfold RDCode.distortion RDCode.castLE
  simp

/-- **Definition (Lecture 3).** A rate–distortion pair `(R, D)`, with `R ≥ 0` in bits per source
symbol, is achievable if there is a sequence of `(2^{nR}, n)` rate–distortion codes, with index set
`[1 : 2^{nR}) = {1, …, 2^⌊nR⌋}`, such that `limsup E d(Xⁿ, X̂ⁿ) ≤ D`. -/
def IsAchievableRDBits (p : α → ℝ) (d : α → β → ℝ) (R D : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ∀ n : ℕ, RDCode (2 ^ ⌊n * R⌋₊) n α β,
    ∀ ε > 0, ∀ᶠ n in atTop, (c n).distortion p d ≤ D + ε

/-- **Definition (Lecture 3).** The rate–distortion function `R(D)`, in bits per source symbol:
the infimum of the rates `R` such that `(R, D)` is achievable. -/
def rateDistortionBits (p : α → ℝ) (d : α → β → ℝ) (D : ℝ) : ℝ :=
  sInf {R | IsAchievableRDBits p d R D}

/-- **Lossy source coding theorem (Lecture 3), achievability.** For `D ≥ D_min`, every rate
`R > R(D)` bits is achievable. -/
theorem isAchievableRDBits_of_lt [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) {R D : ℝ}
    (hD : minDistortion p d ≤ D) (hR : infoRD p d D / log 2 < R) : IsAchievableRDBits p d R D := by
  have hl := log_pos one_lt_two
  have hI := infoRD_nonneg (d := d) hp D
  have hRl : infoRD p d D < R * log 2 := (div_lt_iff₀ hl).1 hR
  have hR0 : 0 < R := by
    have := div_nonneg hI hl.le
    linarith
  obtain ⟨R', hR'1, hR'2⟩ : ∃ R', infoRD p d D < R' ∧ R' < R * log 2 :=
    ⟨(infoRD p d D + R * log 2) / 2, by linarith, by linarith⟩
  obtain ⟨c', hc'⟩ := isAchievableRD_of_infoRD_lt hp hd hD hR'1
  have hR'0 : 0 < R' := hI.trans_lt hR'1
  have hpos : ∀ n : ℕ, 0 < ⌊exp (n * R')⌋₊ := fun n =>
    Nat.floor_pos.2 (one_le_exp (by positivity))
  -- For `n` large, `⌊e^{nR'}⌋ ≤ 2^⌊nR⌋`.
  have hev : ∀ᶠ n : ℕ in atTop, ⌊exp (n * R')⌋₊ ≤ 2 ^ ⌊n * R⌋₊ := by
    have hgap : 0 < R * log 2 - R' := by linarith
    filter_upwards [eventually_ge_atTop ⌈log 2 / (R * log 2 - R')⌉₊] with n hn
    have hn' : log 2 ≤ n * (R * log 2 - R') := (div_le_iff₀ hgap).1 (Nat.ceil_le.1 hn)
    have hfloor : (n * R - 1) * log 2 ≤ ⌊n * R⌋₊ * log 2 :=
      mul_le_mul_of_nonneg_right (by linarith [Nat.lt_floor_add_one (n * R)]) hl.le
    have h2 : exp (n * R') ≤ ((2 ^ ⌊n * R⌋₊ : ℕ) : ℝ) := by
      push_cast
      rw [← exp_log (by positivity : (0 : ℝ) < 2 ^ ⌊n * R⌋₊), log_pow]
      exact exp_le_exp.2 (by nlinarith)
    exact Nat.floor_le_of_le h2
  have hcode : ∀ n : ℕ, ∃ c : RDCode (2 ^ ⌊n * R⌋₊) n α β,
      ⌊exp (n * R')⌋₊ ≤ 2 ^ ⌊n * R⌋₊ → c.distortion p d = (c' n).distortion p d := fun n => by
    by_cases h : ⌊exp (n * R')⌋₊ ≤ 2 ^ ⌊n * R⌋₊
    · exact ⟨(c' n).castLE h (hpos n), fun _ => RDCode.distortion_castLE _ _ _⟩
    · exact ⟨⟨fun _ => ⟨0, by positivity⟩, fun _ _ => Classical.arbitrary β⟩,
        fun h' => absurd h' h⟩
  choose c hc using hcode
  refine ⟨hR0.le, c, fun ε hε => ?_⟩
  filter_upwards [hc' ε hε, hev] with n h1 h2
  rw [hc n h2]
  exact h1

/-- **Lossy source coding theorem (Lecture 3), weak converse.** If `(R, D)` is achievable, then
`R ≥ R(D)` bits. -/
theorem IsAchievableRDBits.infoRD_div_le [Nonempty β] (hp : IsPMF p) {R D : ℝ}
    (h : IsAchievableRDBits p d R D) : infoRD p d D / log 2 ≤ R := by
  obtain ⟨hR0, c, hc⟩ := h
  have hl := log_pos one_lt_two
  rw [div_le_iff₀ hl]
  refine le_of_forall_pos_lt_add fun η hη => ?_
  -- The codes have at most `⌊e^{n(R log 2 + η)}⌋` indices.
  have hle : ∀ n : ℕ, 2 ^ ⌊n * R⌋₊ ≤ ⌊exp (n * (R * log 2 + η / 2))⌋₊ := fun n => by
    refine Nat.le_floor ?_
    push_cast
    calc (2 : ℝ) ^ ⌊n * R⌋₊ = exp (⌊n * R⌋₊ * log 2) := by
          rw [← exp_log (by positivity : (0 : ℝ) < 2 ^ ⌊n * R⌋₊), log_pow]
      _ ≤ exp (n * (R * log 2 + η / 2)) := by
          refine exp_le_exp.2 ?_
          have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hR0)
          nlinarith [mul_le_mul_of_nonneg_right this hl.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hach : IsAchievableRD p d (R * log 2 + η / 2) D :=
    ⟨fun n => (c n).castLE (hle n) (by positivity), fun ε hε => by
      filter_upwards [hc ε hε] with n hn
      rwa [RDCode.distortion_castLE]⟩
  have := hach.infoRD_le hp
  linarith

/-- **Shannon's lossy source coding theorem (Lecture 3).** For `D ≥ D_min`, the rate–distortion
function of a discrete memoryless source is
`R(D) = min_{p(x̂|x) : E d(X, X̂) ≤ D} I(X; X̂)`, in bits. -/
theorem rateDistortionBits_eq [Nonempty β] (hp : IsPMF p) (hd : ∀ x y, 0 ≤ d x y) {D : ℝ}
    (hD : minDistortion p d ≤ D) : rateDistortionBits p d D = infoRD p d D / log 2 :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    ⟨infoRD p d D / log 2 + 1, isAchievableRDBits_of_lt hp hd hD (by linarith)⟩
    (fun R hR => hR.infoRD_div_le hp) fun w hw =>
      ⟨(infoRD p d D / log 2 + w) / 2, isAchievableRDBits_of_lt hp hd hD (by linarith),
        by linarith⟩

/-! ### Lossless source coding as a special case -/

/-- **Lossless source coding revisited (Lecture 3).** For the Hamming distortion,
`R(0) = min_{p(x̂|x) : E d(X, X̂) = 0} I(X; X̂) = H(X)`. -/
theorem infoRD_hammingDistortion_zero (hp : IsPMF p) :
    infoRD p hammingDistortion 0 = entropy p := by
  classical
  -- A channel with zero expected Hamming distortion reproduces every symbol of positive
  -- probability.
  have key : ∀ q : α → α → ℝ, IsChannel q → expDistortion p q hammingDistortion ≤ 0 →
      mutualInfoOf p q = entropy p := by
    intro q hq hD
    have hterm : ∀ x y, p x * q x y * hammingDistortion x y = 0 := by
      have hnn : ∀ x y, 0 ≤ p x * q x y * hammingDistortion x y := fun x y =>
        mul_nonneg (mul_nonneg (hp.nonneg x) ((hq x).nonneg y))
          (by unfold hammingDistortion; split_ifs <;> norm_num)
      have hsum : ∑ x, ∑ y, p x * q x y * hammingDistortion x y = 0 :=
        le_antisymm hD (sum_nonneg fun x _ => sum_nonneg fun y _ => hnn x y)
      intro x y
      exact (sum_eq_zero_iff_of_nonneg fun y _ => hnn x y).1
        ((sum_eq_zero_iff_of_nonneg fun x _ => sum_nonneg fun y _ => hnn x y).1 hsum x
          (mem_univ x)) y (mem_univ y)
    -- For `p(x) > 0`, the row `q(·|x)` is the point mass at `x`.
    have hrow : ∀ x, 0 < p x → q x = fun y => if y = x then 1 else 0 := fun x hx => by
      have hoff : ∀ y, y ≠ x → q x y = 0 := fun y hy => by
        have := hterm x y
        rw [hammingDistortion, ite_eq_right (Ne.symm hy), mul_one] at this
        exact (mul_eq_zero.1 this).resolve_left hx.ne'
      have hsum := (hq x).sum_eq_one
      rw [sum_eq_single x (fun y _ hy => hoff y hy) (by simp)] at hsum
      funext y
      by_cases hy : y = x
      · subst hy; simp [hsum]
      · simp [hy, hoff y hy]
    rw [mutualInfoOf_eq hp hq]
    have hout : outDist p q = p := by
      funext y
      rw [outDist, sum_eq_single y]
      · rcases (hp.nonneg y).eq_or_lt with h | h
        · rw [← h, zero_mul]
        · rw [hrow y h]; simp
      · intro x _ hxy
        rcases (hp.nonneg x).eq_or_lt with h | h
        · rw [← h, zero_mul]
        · rw [hrow x h]; simp [Ne.symm hxy]
      · simp
    have hcond : ∑ x, p x * entropy (q x) = 0 := by
      refine sum_eq_zero fun x _ => ?_
      rcases (hp.nonneg x).eq_or_lt with h | h
      · rw [← h, zero_mul]
      · rw [hrow x h, entropy_eq_sum_negMulLog]
        simp [apply_ite negMulLog]
    rw [hout, hcond, sub_zero]
  have hset : {I | ∃ q : α → α → ℝ, IsChannel q ∧ expDistortion p q hammingDistortion ≤ 0 ∧
      mutualInfoOf p q = I} = {entropy p} := by
    ext I
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨q, hq, hD, rfl⟩
      exact key q hq hD
    · rintro rfl
      refine ⟨detChannel id, detChannel_isChannel id, ?_, key _ (detChannel_isChannel id) ?_⟩ <;>
      · rw [expDistortion_detChannel]
        simp [hammingDistortion]
  rw [infoRD, hset, csInf_singleton]

end InfoTheory
