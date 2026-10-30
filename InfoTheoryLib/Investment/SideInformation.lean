/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Investment.KuhnTucker
public import InfoTheoryLib.MutualInformation.Basic

/-!
# Side information and the growth rate

Investing with the log-optimal portfolio `b_g` of a wrong distribution `g` instead of the
log-optimal portfolio of the true distribution `f` costs at most `D(f‖g)` in growth rate
(Theorem 16.4.1). Side information `Y` about the market `X` increases the growth rate by at most
`I(X; Y)` (Theorem 16.4.2), with equality for a horse race.

Both bounds come from a single inequality: for any portfolio `b` and the log-optimal portfolio
`b_g` of `g`, `W(b, f) - W(b_g, f) ≤ D(f‖g)`, from `log t ≤ t - 1` and the Kuhn–Tucker condition
`E_g(bᵗX / b_gᵗX) ≤ 1`, (16.40)–(16.47). We state it for unnormalized weights `r` with total mass
`R`, which gives the side information bound without forming conditional distributions.

## Main statements

* `growthRate_sub_le_of_absCont`: `W(b, r) - W(b_g, r) ≤ ∑ₖ r(k) log (r(k) / (R g(k)))`.
* `growthRate_sub_le_relEntropy`: **Theorem 16.4.1**, `ΔW ≤ D(f‖g)`, (16.39).
* `sideInfo_gain_le`: **Theorem 16.4.2**, `ΔW ≤ I(X; Y)`, (16.48).

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 16.4
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {m : ℕ} {ι : Type*} [Fintype ι] {x : ι → Fin m → ℝ}

/-- **(16.40)–(16.47)** For nonnegative weights `r` of total mass `R`, absolutely continuous with
respect to a pmf `g`, any portfolio `b` and the log-optimal portfolio `b_g` of `g` satisfy
`W(b, r) - W(b_g, r) ≤ ∑ₖ r(k) log (r(k) / (R g(k)))`. -/
theorem growthRate_sub_le_of_absCont {r G : ι → ℝ} (hr : ∀ k, 0 ≤ r k) (hG : IsPMF G)
    (habs : ∀ k, G k = 0 → r k = 0) (hx : IsPosMarket x) {b bG : Fin m → ℝ} (hb : IsPMF b)
    (hbG : IsLogOptimal G x bG) :
    growthRate b r x - growthRate bG r x ≤ ∑ k, r k * log (r k / (G k * ∑ k', r k')) := by
  set R := ∑ k', r k'
  have hR : 0 ≤ R := sum_nonneg fun k _ => hr k
  have hKT := hbG.sum_ratio_le hG.nonneg hx hb
  rw [hG.sum_eq_one] at hKT
  rw [growthRate_sub_eq hx hbG.1 hb, ← sub_nonneg, ← sum_sub_distrib]
  -- Termwise: `r log (S/S_g) - r log (r/(R g)) ≤ R g S/S_g - r`.
  have hterm : ∀ k, r k * log (wealthRel b (x k) / wealthRel bG (x k)) -
      r k * log (r k / (G k * R)) ≤
      R * (G k * (wealthRel b (x k) / wealthRel bG (x k))) - r k := by
    intro k
    have hS := wealthRel_pos hb (hx k)
    have hSG := wealthRel_pos hbG.1 (hx k)
    have hq : 0 < wealthRel b (x k) / wealthRel bG (x k) := div_pos hS hSG
    rcases (hr k).lt_or_eq with hrk | hrk
    · have hGk : 0 < G k := (hG.nonneg k).lt_of_ne fun h => hrk.ne' (habs k h.symm)
      have hRpos : 0 < R := lt_of_lt_of_le hrk (single_le_sum (fun k _ => hr k) (mem_univ k))
      have e : r k * log (wealthRel b (x k) / wealthRel bG (x k)) - r k * log (r k / (G k * R)) =
          r k * log (wealthRel b (x k) / wealthRel bG (x k) * (G k * R) / r k) := by
        rw [log_div (by positivity) hrk.ne', log_mul hq.ne' (by positivity),
          log_div hrk.ne' (by positivity)]
        ring
      rw [e]
      have h := log_le_sub_one_of_pos
        (show 0 < wealthRel b (x k) / wealthRel bG (x k) * (G k * R) / r k by positivity)
      have e2 : r k * (wealthRel b (x k) / wealthRel bG (x k) * (G k * R) / r k - 1) =
          R * (G k * (wealthRel b (x k) / wealthRel bG (x k))) - r k := by
        field_simp
      rw [← e2]
      exact mul_le_mul_of_nonneg_left h hrk.le
    · rw [← hrk]
      simp only [zero_mul, sub_zero]
      have : 0 ≤ R * (G k * (wealthRel b (x k) / wealthRel bG (x k))) :=
        mul_nonneg hR (mul_nonneg (hG.nonneg k) hq.le)
      linarith
  have hsum := sum_le_sum fun k (_ : k ∈ univ) => hterm k
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum] at hsum
  have : R * ∑ k, G k * (wealthRel b (x k) / wealthRel bG (x k)) ≤ R :=
    (mul_le_mul_of_nonneg_left hKT hR).trans (by rw [mul_one])
  have e3 : ∑ k, r k * log (r k / (G k * R)) = ∑ k, r k * log (r k / (G k * ∑ k', r k')) := rfl
  rw [sum_sub_distrib]
  linarith

/-- **Theorem 16.4.1, (16.39).** Using the log-optimal portfolio `b_g` of a wrong distribution `g`
instead of the log-optimal portfolio `b_f` of the true distribution `f` decreases the growth rate
by at most `D(f‖g)`: `W(b_f, f) - W(b_g, f) ≤ D(f‖g)`. -/
theorem growthRate_sub_le_relEntropy {f g : ι → ℝ} (hf : IsPMF f) (hg : IsPMF g)
    (habs : AbsCont f g) (hx : IsPosMarket x) {bf bg : Fin m → ℝ} (hbf : IsPMF bf)
    (hbg : IsLogOptimal g x bg) :
    growthRate bf f x - growthRate bg f x ≤ relEntropyReal f g := by
  have h := growthRate_sub_le_of_absCont hf.nonneg hg habs hx hbf hbg
  rw [hf.sum_eq_one] at h
  simpa only [mul_one, relEntropyReal] using h

variable {γ : Type*} [Fintype γ]

/-- **Theorem 16.4.2, (16.48)–(16.53).** Side information `Y` about the market `X`, with joint pmf
`q(x, y)`, increases the optimal growth rate by at most `I(X; Y)`: the investor who knows `Y = y`
uses the log-optimal portfolio of `q(·, y)`, and
`∑_y W*(q(·, y)) - W*(q_X) ≤ I(X; Y)`. Since `W*` is homogeneous,
`W*(q(·, y)) = q(y) W*(q(· | y))`. -/
theorem sideInfo_gain_le (hm : 0 < m) {q : ι × γ → ℝ} (hq : IsPMF q) (hx : IsPosMarket x) :
    ∑ y, optGrowthRate (fun k => q (k, y)) x - optGrowthRate (dist q Prod.fst) x ≤
      I[Prod.fst : Prod.snd ; q] := by
  set p := dist q Prod.fst
  have hp : IsPMF p := hq.dist _
  obtain ⟨b₀, hb₀⟩ := exists_isLogOptimal hm hx p
  have hpk : ∀ k, p k = ∑ y, q (k, y) := fun k => dist_fst q k
  -- `∑_y W(b₀, q(·, y)) = W(b₀, p) = W*(p)`.
  have hlin : ∑ y, growthRate b₀ (fun k => q (k, y)) x = optGrowthRate p x := by
    rw [hb₀.optGrowthRate_eq]
    simp only [growthRate, hpk, sum_mul]
    exact sum_comm
  -- For each `y`, apply the bound with `g = p`.
  have hy : ∀ y, optGrowthRate (fun k => q (k, y)) x - growthRate b₀ (fun k => q (k, y)) x ≤
      ∑ k, q (k, y) * log (q (k, y) / (p k * ∑ k', q (k', y))) := by
    intro y
    obtain ⟨b, hb⟩ := exists_isLogOptimal hm hx (fun k => q (k, y))
    rw [hb.optGrowthRate_eq]
    refine growthRate_sub_le_of_absCont (fun k => hq.nonneg _) hp (fun k hk => ?_) hx hb.1 hb₀
    have hle : q (k, y) ≤ p k := by
      rw [hpk]
      exact single_le_sum (f := fun y => q (k, y)) (fun y _ => hq.nonneg _) (mem_univ y)
    exact le_antisymm (hk ▸ hle) (hq.nonneg _)
  have hI : I[Prod.fst : Prod.snd ; q] =
      ∑ y, ∑ k, q (k, y) * log (q (k, y) / (p k * ∑ k', q (k', y))) := by
    rw [mutualInfo_eq_sum, sum_comm]
    refine sum_congr rfl fun y _ => sum_congr rfl fun k _ => ?_
    rw [dist_pair_fst_snd, dist_snd]
  have := sum_le_sum fun y (_ : y ∈ univ) => hy y
  rw [sum_sub_distrib, hlin] at this
  rw [hI]
  exact this

end InfoTheory
