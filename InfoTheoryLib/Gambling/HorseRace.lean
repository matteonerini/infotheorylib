/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RelativeEntropy.InformationInequality
public import InfoTheoryLib.Probability.WeakLaw

/-!
# The horse race

Horse `x` wins a race with probability `p(x)` and pays `o(x)`-for-`1`. A gambler invests the
fraction `b(x)` of their wealth on horse `x` (`b` is a pmf: the gambler is fully invested). If horse
`x` wins, the wealth is multiplied by the wealth relative `S(x) = b(x) o(x)`. Over repeated
independent races the wealth grows exponentially at the doubling rate `W(b, p) = E log S(X)`, which
is maximized by proportional gambling `b = p`.

Logarithms are natural, so doubling rates are in nats per race. The book uses base 2, so its
`W` is `W / log 2` and its `2^{nW}` is our `exp (n W)`.

## Main definitions

* `doublingRate b o p`: the doubling rate `W(b, p) = ∑ p(x) log b(x) o(x)`, (6.2).
* `wealth b o x`: the wealth `Sₙ = ∏ᵢ S(xᵢ)` after the races `x₁, …, xₙ`, (6.1).
* `optDoublingRate o p`: the optimal doubling rate `W*(p) = max_b W(b, p)`, (6.6).
* `cashDoublingRate b₀ b o p`: the doubling rate when the fraction `b₀` is kept as cash, (6.21).

## Main statements

* `log_wealth_div_tendstoInProb`: Theorem 6.1.1, `(1/n) log Sₙ → W(b, p)` in probability.
* `doublingRate_eq`, `doublingRate_le`, `doublingRate_eq_iff`, `optDoublingRate_eq`:
  Theorem 6.1.2, proportional gambling is log-optimal, `W*(p) = ∑ p(x) log o(x) - H(p)`.
* `doublingRate_eq_relEntropy_sub`: (6.16)–(6.18), for odds `o = 1/r`,
  `W(b, p) = D(p‖r) - D(p‖b)`.
* `optDoublingRate_uniform`, `optDoublingRate_add_entropy`: (6.19) and Theorem 6.1.3 (conservation
  theorem), `W*(p) + H(p) = log m` for uniform fair odds.
* `cashDoublingRate_le`: with fair or superfair odds, keeping cash does not beat proportional
  betting (subcases 1 and 2 of Section 6.1).
* `dutchBook_wealthRelative`: a Dutch book with superfair odds gains for sure.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 6.1
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {α : Type*} [Fintype α]

/-- **Definition (6.2).** The doubling rate `W(b, p) = E log S(X) = ∑ₓ p(x) log b(x) o(x)` of the
betting scheme `b` with odds `o` when horse `x` wins with probability `p(x)`. -/
def doublingRate (b o p : α → ℝ) : ℝ := ∑ x, p x * log (b x * o x)

/-- **(6.1)** The wealth `Sₙ = ∏ᵢ S(xᵢ)` after the races `x₁, …, xₙ`, starting from one unit and
reinvesting, where `S(x) = b(x) o(x)` is the wealth relative. -/
def wealth (b o : α → ℝ) {n : ℕ} (x : Fin n → α) : ℝ := ∏ i, b (x i) * o (x i)

/-- **Theorem 6.1.1, (6.3)–(6.5).** If the races are i.i.d. with law `p`, the wealth grows
exponentially at rate `W(b, p)`: `(1/n) log Sₙ → W(b, p)` in probability. We assume a positive
bet on every horse, which keeps `log Sₙ` finite. -/
theorem log_wealth_div_tendstoInProb {p b o : α → ℝ} (hp : IsPMF p)
    (hbo : ∀ x, 0 < b x * o x) :
    TendstoInProb (fun n => iidPMF p n) (fun n x => log (wealth b o x) / n)
      (doublingRate b o p) := by
  have h := weak_law hp fun x => log (b x * o x)
  have heq : (fun n (x : Fin n → α) => log (wealth b o x) / n) =
      fun n x => sampleMean fun i => log (b (x i) * o (x i)) := by
    funext n x
    rw [wealth, log_prod fun i _ => (hbo _).ne', sampleMean, Fintype.card_fin]
  have hW : expect p (fun x => log (b x * o x)) = doublingRate b o p := by
    simp only [expect, doublingRate, mul_comm]
  rw [heq, ← hW]
  exact h

/-! ### Proportional gambling -/

/-- **(6.11)–(6.13)** `W(b, p) = ∑ p(x) log o(x) - H(p) - D(p‖b)`, if the gambler bets on every
horse that can win (`p ≪ b`; otherwise `W(b, p) = -∞`). -/
theorem doublingRate_eq {p b o : α → ℝ} (hp : IsPMF p) (hb : ∀ x, 0 ≤ b x) (hpb : AbsCont p b)
    (ho : ∀ x, 0 < o x) :
    doublingRate b o p = ∑ x, p x * log (o x) - entropy p - relEntropyReal p b := by
  have : ∑ x, p x * log (o x) - entropy p - relEntropyReal p b =
      ∑ x, (p x * log (o x) + p x * log (p x) - p x * log (p x / b x)) := by
    simp only [entropy, relEntropyReal, sum_add_distrib, sum_sub_distrib]
    ring
  rw [this, doublingRate]
  refine sum_congr rfl fun x _ => ?_
  rcases (hp.nonneg x).eq_or_lt with h0 | h0
  · simp [← h0]
  · have hbx : 0 < b x := (hb x).lt_of_ne fun h => h0.ne' (hpb x h.symm)
    rw [log_mul hbx.ne' (ho x).ne', log_div h0.ne' hbx.ne']
    ring

/-- **(6.14)** `W(b, p) ≤ ∑ p(x) log o(x) - H(p)`. -/
theorem doublingRate_le {p b o : α → ℝ} (hp : IsPMF p) (hb : IsPMF b) (hpb : AbsCont p b)
    (ho : ∀ x, 0 < o x) : doublingRate b o p ≤ ∑ x, p x * log (o x) - entropy p := by
  rw [doublingRate_eq hp hb.nonneg hpb ho]
  linarith [relEntropyReal_nonneg hp hb hpb]

/-- **Theorem 6.1.2 (equality).** Equality holds in `W(b, p) ≤ ∑ p(x) log o(x) - H(p)` iff the
gambler bets proportionally, `b = p`. -/
theorem doublingRate_eq_iff {p b o : α → ℝ} (hp : IsPMF p) (hb : IsPMF b) (hpb : AbsCont p b)
    (ho : ∀ x, 0 < o x) :
    doublingRate b o p = ∑ x, p x * log (o x) - entropy p ↔ b = p := by
  rw [doublingRate_eq hp hb.nonneg hpb ho, eq_comm (a := b)]
  rw [← relEntropyReal_eq_zero_iff hp hb hpb]
  constructor <;> intro h <;> linarith

/-- Proportional gambling achieves `W(p, p) = ∑ p(x) log o(x) - H(p)`. -/
theorem doublingRate_self {p o : α → ℝ} (hp : IsPMF p) (ho : ∀ x, 0 < o x) :
    doublingRate p o p = ∑ x, p x * log (o x) - entropy p :=
  (doublingRate_eq_iff hp hp (fun _ h => h) ho).2 rfl

/-- **Definition (6.6).** The optimal doubling rate `W*(p) = max_b W(b, p)`, over the betting
schemes that bet on every horse that can win. -/
def optDoublingRate (o p : α → ℝ) : ℝ :=
  sSup {w | ∃ b, IsPMF b ∧ AbsCont p b ∧ doublingRate b o p = w}

/-- **Theorem 6.1.2 (Proportional gambling is log-optimal), (6.10).** The optimal doubling rate is
`W*(p) = ∑ p(x) log o(x) - H(p)`, achieved by proportional gambling `b* = p`. -/
theorem optDoublingRate_eq {p o : α → ℝ} (hp : IsPMF p) (ho : ∀ x, 0 < o x) :
    optDoublingRate o p = ∑ x, p x * log (o x) - entropy p :=
  IsGreatest.csSup_eq ⟨⟨p, hp, fun _ h => h, doublingRate_self hp ho⟩,
    fun _ ⟨_, hb, hpb, hw⟩ => hw ▸ doublingRate_le hp hb hpb ho⟩

/-! ### Fair odds -/

/-- **(6.16)–(6.18)** With odds `o(x) = 1/r(x)`, where `r` is the bookie's estimate of the win
probabilities (the odds are fair when `∑ 1/o(x) = 1`), the doubling rate is
`W(b, p) = D(p‖r) - D(p‖b)`: the gambler makes money only if their estimate `b` is closer to `p`
than the bookie's. -/
theorem doublingRate_eq_relEntropy_sub {p b o : α → ℝ} (hp : IsPMF p) (hb : ∀ x, 0 ≤ b x)
    (hpb : AbsCont p b) (ho : ∀ x, 0 < o x) :
    doublingRate b o p = relEntropyReal p (fun x => 1 / o x) - relEntropyReal p b := by
  rw [doublingRate, relEntropyReal, relEntropyReal, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rcases (hp.nonneg x).eq_or_lt with h0 | h0
  · simp [← h0]
  · have hbx : 0 < b x := (hb x).lt_of_ne fun h => h0.ne' (hpb x h.symm)
    rw [show p x / (1 / o x) = p x * o x by field_simp, log_mul hbx.ne' (ho x).ne',
      log_mul h0.ne' (ho x).ne',
      log_div h0.ne' hbx.ne']
    ring

/-- **(6.19)** With `m`-for-`1` odds on each of the `m` horses (fair odds for the uniform
distribution), `W*(p) = D(p‖u) = log m - H(p)`. -/
theorem optDoublingRate_uniform {p : α → ℝ} (hp : IsPMF p) :
    optDoublingRate (fun _ => (Fintype.card α : ℝ)) p = relEntropyReal p (uniformPMF α) ∧
      optDoublingRate (fun _ => (Fintype.card α : ℝ)) p = log (Fintype.card α) - entropy p := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast card_pos_of_isPMF hp
  have h : optDoublingRate (fun _ => (Fintype.card α : ℝ)) p =
      log (Fintype.card α) - entropy p := by
    rw [optDoublingRate_eq hp fun _ => hc, ← sum_mul, hp.sum_eq_one, one_mul]
  exact ⟨h.trans (relEntropyReal_uniform hp).symm, h⟩

/-- **Theorem 6.1.3 (Conservation theorem), (6.20).** For uniform fair odds,
`W*(p) + H(p) = log m`: the doubling rate and the entropy add up to a constant. -/
theorem optDoublingRate_add_entropy {p : α → ℝ} (hp : IsPMF p) :
    optDoublingRate (fun _ => (Fintype.card α : ℝ)) p + entropy p = log (Fintype.card α) := by
  rw [(optDoublingRate_uniform hp).2]
  ring

/-! ### Keeping cash -/

/-- **(6.21)** The doubling rate `E log (b₀ + b(X) o(X))` when the fraction `b₀` of the wealth is
kept as cash and `b(x)` is bet on horse `x`, with `b₀ + ∑ b(x) = 1`. -/
def cashDoublingRate (b₀ : ℝ) (b o p : α → ℝ) : ℝ := ∑ x, p x * log (b₀ + b x * o x)

/-- **Section 6.1, subcases 1 and 2.** With fair (`∑ 1/o(x) = 1`) or superfair
(`∑ 1/o(x) < 1`) odds, keeping cash does not help: the doubling rate of any scheme with cash is at
most the optimal doubling rate `∑ p(x) log o(x) - H(p)` of proportional betting without cash.
Indeed the cash `b₀` can be spread as `b₀ / o(x)` over the horses, which returns at least `b₀`
whichever horse wins. -/
theorem cashDoublingRate_le {p b o : α → ℝ} {b₀ : ℝ} (hp : IsPMF p) (hb₀ : 0 ≤ b₀)
    (hb : ∀ x, 0 ≤ b x) (hsum : b₀ + ∑ x, b x = 1) (ho : ∀ x, 0 < o x)
    (hfair : ∑ x, 1 / o x ≤ 1) (hpos : ∀ x, p x ≠ 0 → 0 < b₀ + b x * o x) :
    cashDoublingRate b₀ b o p ≤ ∑ x, p x * log (o x) - entropy p := by
  -- Spread the cash over the horses: `b' x = b x + b₀ / o x`, then normalize.
  set b' : α → ℝ := fun x => b x + b₀ / o x
  set c := ∑ x, b' x
  have hb' : ∀ x, 0 ≤ b' x := fun x => add_nonneg (hb x) (div_nonneg hb₀ (ho x).le)
  have hb'o : ∀ x, b' x * o x = b₀ + b x * o x := fun x => by
    simp only [b']
    field_simp [(ho x).ne']
    ring
  have hc1 : c ≤ 1 := by
    have : c = ∑ x, b x + b₀ * ∑ x, 1 / o x := by
      simp only [c, b', sum_add_distrib, mul_sum, mul_one_div]
    rw [this]
    nlinarith
  obtain ⟨x₀, hx₀⟩ : ∃ x, p x ≠ 0 := by
    by_contra h
    push Not at h
    have := hp.sum_eq_one
    simp [h] at this
  have hc0 : 0 < c := by
    have h1 : 0 < b' x₀ := by
      have := hpos x₀ hx₀
      rw [← hb'o] at this
      exact pos_of_mul_pos_left this (ho x₀).le
    exact lt_of_lt_of_le h1 (single_le_sum (fun x _ => hb' x) (mem_univ x₀))
  set b'' : α → ℝ := fun x => b' x / c
  have hb'' : IsPMF b'' := ⟨fun x => div_nonneg (hb' x) hc0.le, by
    simp only [b'', ← sum_div]
    exact div_self hc0.ne'⟩
  have hle : ∀ x, b₀ + b x * o x ≤ b'' x * o x := fun x => by
    simp only [b'', div_mul_eq_mul_div, hb'o]
    rw [le_div_iff₀ hc0]
    exact mul_le_of_le_one_right (by rw [← hb'o]; exact mul_nonneg (hb' x) (ho x).le) hc1
  have hpb : AbsCont p b'' := fun x hx => by
    by_contra hpx
    have := (hpos x hpx).trans_le (hle x)
    rw [hx, zero_mul] at this
    exact lt_irrefl 0 this
  calc cashDoublingRate b₀ b o p ≤ doublingRate b'' o p :=
        sum_le_sum fun x _ => by
          rcases (hp.nonneg x).eq_or_lt with h0 | h0
          · simp [← h0]
          · exact mul_le_mul_of_nonneg_left (log_le_log (hpos x h0.ne') (hle x)) h0.le
    _ ≤ _ := doublingRate_le hp hb'' hpb ho

/-- **Section 6.1, subcase 2 (Dutch book).** With superfair odds, `∑ 1/o(x) < 1`, the bet
`b(x) = c/o(x)` with `c = 1/∑ 1/o(x)` is a bet, `∑ b(x) = 1`, and returns `b(x) o(x) = c > 1`
whichever horse `x` wins: a gain with no risk. -/
theorem dutchBook_wealthRelative {o : α → ℝ} (ho : ∀ x, 0 < o x) (hsf : ∑ y, 1 / o y < 1)
    (x : α) :
    ∑ y, 1 / o y / (∑ z, 1 / o z) = 1 ∧ 1 / o x / (∑ y, 1 / o y) * o x = 1 / ∑ y, 1 / o y ∧
      1 < 1 / ∑ y, 1 / o y := by
  have hs : 0 < ∑ y, 1 / o y := (one_div_pos.2 (ho x)).trans_le
    (single_le_sum (fun y _ => (one_div_pos.2 (ho y)).le) (mem_univ x))
  refine ⟨by rw [← sum_div, div_self hs.ne'], ?_, (one_lt_div hs).2 hsf⟩
  field_simp [(ho x).ne']

end InfoTheory
