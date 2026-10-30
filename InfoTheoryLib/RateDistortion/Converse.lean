/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.RateDistortion.Basic
public import InfoTheoryLib.MutualInformation.ChainRule
public import InfoTheoryLib.Entropy.Bounds

/-!
# The converse to the rate distortion theorem

Any `(M, n)` rate distortion code with distortion `D` for an i.i.d. source has
`log M ≥ n R^(I)(D)`. Hence every achievable pair `(R, D)` has `R ≥ R^(I)(D)`.

## Main statements

* `sum_mutualInfo_le_of_indepFamily`: (10.62)–(10.66), for independent `X₁, …, Xₙ` and any `X̂ⁿ`,
  `I(Xⁿ; X̂ⁿ) ≥ ∑ᵢ I(Xᵢ; X̂ᵢ)`.
* `mul_infoRD_le_mutualInfo`: (10.61)–(10.71), `I(Xⁿ; X̂ⁿ) ≥ n R^(I)(E d(Xⁿ, X̂ⁿ))` for an i.i.d.
  source `Xⁿ` and any reproduction `X̂ⁿ`.
* `RDCode.minDistortion_le_distortion`: no code has distortion below `D_min`.
* `RDCode.mul_infoRD_le_log`: **(10.58)–(10.71)**, `n R^(I)(D) ≤ log M` for every `(M, n)` code
  with distortion `D`.
* `IsAchievableRD.infoRD_le`: **Theorem 10.2.1 (converse)**, an achievable pair has
  `R ≥ R^(I)(D)`.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 10.4
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]

/-! ### Mutual information with an independent family -/

/-- **(10.62)–(10.66)** If `X₁, …, Xₙ` are independent, then `I(Xⁿ; Y) ≥ ∑ᵢ I(Xᵢ; gᵢ(Y))` for any
`Y` and any functions `gᵢ`: `H(Xⁿ) = ∑ᵢ H(Xᵢ)`, and by the chain rule
`H(Xⁿ | Y) = ∑ᵢ H(Xᵢ | Y, X^{i-1}) ≤ ∑ᵢ H(Xᵢ | gᵢ(Y))`. -/
theorem sum_mutualInfo_le_of_indepFamily {μ : Ω → ℝ} (hμ : IsPMF μ) {X : ℕ → Ω → α} {n : ℕ}
    (hX : IndepFamily μ X n) (Y : Ω → γ) (g : ℕ → γ → β) :
    ∑ i ∈ range n, I[X i : g i ∘ Y ; μ] ≤ I[prefixRV X n : Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, (entropy_prefixRV_eq_sum_iff hμ X n).2 hX,
    chain_rule_entropy_cond hμ, ← sum_sub_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ]
  have h1 : H[X i | pair Y (prefixRV X i) ; μ] = H[X i | pair (prefixRV X i) Y ; μ] :=
    (condEntropy_congr_right hμ (X i) Prod.swap Prod.swap_injective fun _ => rfl).symm
  have h2 := condEntropy_le_condEntropy hμ (X i) (prefixRV X i) Y
  have h3 : H[X i | pair Y (g i ∘ Y) ; μ] = H[X i | Y ; μ] :=
    condEntropy_congr_right hμ (X i) (fun y => (y, g i y))
      (fun a b h => (Prod.mk.inj h).1) fun _ => rfl
  have h4 := condEntropy_le_condEntropy hμ (X i) Y (g i ∘ Y)
  linarith

/-! ### The coordinates of an i.i.d. sequence -/

omit [Fintype α] in
/-- The coordinates `X₀, X₁, …` of a sequence in `𝒳ⁿ`, extended by `a₀` beyond `n`. -/
def coordRV (n : ℕ) (a₀ : α) (i : ℕ) (x : Fin n → α) : α := if h : i < n then x ⟨i, h⟩ else a₀

omit [Fintype α] in
lemma prefixRV_coordRV (n : ℕ) (a₀ : α) : prefixRV (coordRV n a₀) n = id := by
  funext x i
  simp [prefixRV, coordRV]

lemma indepFamily_coordRV {p : α → ℝ} (hp : IsPMF p) (n : ℕ) (a₀ : α) :
    IndepFamily (iidPMF p n) (coordRV n a₀) n := by
  intro v
  rw [prefixRV_coordRV, dist_id]
  refine prod_congr rfl fun i _ => ?_
  have : coordRV n a₀ i = fun x : Fin n → α => x i := by
    funext x
    simp [coordRV]
  rw [this, dist_iidPMF_apply hp]

/-! ### The converse for a block of the source -/

section Block

variable {p : α → ℝ} {d : α → β → ℝ}

/-- **(10.61)–(10.71)** For `n` i.i.d. source letters `Xⁿ ∼ p` and any reproduction `X̂ⁿ`,
`I(Xⁿ; X̂ⁿ) ≥ ∑ᵢ I(Xᵢ; X̂ᵢ) ≥ ∑ᵢ R^(I)(E d(Xᵢ, X̂ᵢ)) ≥ n R^(I)(E d(Xⁿ, X̂ⁿ))`, by the independence
of the `Xᵢ`, the convexity of `R^(I)` and Jensen's inequality. -/
theorem mul_infoRD_le_mutualInfo [Nonempty β] (hp : IsPMF p) {μ : Ω → ℝ} (hμ : IsPMF μ) {n : ℕ}
    (hn : 0 < n) {V : Ω → Fin n → α} (hV : dist μ V = iidPMF p n) (Y : Ω → Fin n → β) :
    n * infoRD p d (∑ ω, μ ω * seqDistortion d (V ω) (Y ω)) ≤ I[V : Y ; μ] := by
  classical
  have : Nonempty α := by
    obtain ⟨a, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hp)
    exact ⟨a⟩
  set a₀ := Classical.arbitrary α
  set b₀ := Classical.arbitrary β
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set X : ℕ → Ω → α := fun i ω => coordRV n a₀ i (V ω)
  set g : ℕ → (Fin n → β) → β := coordRV n b₀
  have hpre : prefixRV X n = V := by
    funext ω i
    simp [prefixRV, X, coordRV]
  -- Each letter `Xᵢ` has law `p`, and the letters are independent.
  have hlaw : ∀ i : Fin n, dist μ (fun ω => V ω i) = p := fun i => by
    rw [show (fun ω => V ω i) = (fun x : Fin n → α => x i) ∘ V from rfl, dist_comp_eq, hV,
      dist_iidPMF_apply hp]
  have hcoord : ∀ i : Fin n, X i = fun ω => V ω i := fun i => by
    funext ω; simp [X, coordRV]
  have hgcoord : ∀ i : Fin n, g i ∘ Y = fun ω => Y ω i := fun i => by
    funext ω; simp [g, coordRV]
  have hind : IndepFamily μ X n := by
    intro v
    rw [hpre, hV]
    exact prod_congr rfl fun i _ => by rw [hcoord i, hlaw i]
  have h2 := sum_mutualInfo_le_of_indepFamily hμ hind Y g
  rw [hpre] at h2
  -- The letter distortions `Dᵢ = E d(Xᵢ, X̂ᵢ) ≥ D_min`.
  set Dl : Fin n → ℝ := fun i => ∑ ω, μ ω * d (V ω i) (Y ω i)
  have hDl : ∀ i, minDistortion p d ≤ Dl i := fun i => by
    have h := sum_dist_mul μ (fun ω => V ω i) fun a => ⨅ y, d a y
    rw [hlaw i] at h
    calc minDistortion p d = ∑ ω, μ ω * ⨅ y, d (V ω i) y := h
      _ ≤ Dl i := sum_le_sum fun ω _ =>
          mul_le_mul_of_nonneg_left (ciInf_le_distortion d _ _) (hμ.nonneg ω)
  have h3 : ∀ i : Fin n, infoRD p d (Dl i) ≤ I[X i : g i ∘ Y ; μ] := by
    intro i
    rw [hcoord i, hgcoord i]
    exact infoRD_le_mutualInfo hp hμ (hlaw i)
  have hsum : ∑ i : Fin n, infoRD p d (Dl i) ≤ ∑ i ∈ range n, I[X i : g i ∘ Y ; μ] := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => I[X i : g i ∘ Y ; μ])]
    exact sum_le_sum fun i _ => h3 i
  -- Jensen's inequality for the convex function `R^(I)`.
  have hJ := (infoRD_convexOn (d := d) hp).map_sum_le (t := univ)
    (w := fun _ : Fin n => 1 / (n : ℝ)) (p := Dl) (fun _ _ => by positivity)
    (by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
    fun i _ => hDl i
  simp only [smul_eq_mul, ← mul_sum] at hJ
  have hD : 1 / n * ∑ i, Dl i = ∑ ω, μ ω * seqDistortion d (V ω) (Y ω) := by
    simp only [Dl, seqDistortion, mul_sum, mul_div_assoc']
    rw [sum_comm]
    exact sum_congr rfl fun ω _ => by rw [sum_div]; exact sum_congr rfl fun i _ => by ring
  rw [hD] at hJ
  calc n * infoRD p d (∑ ω, μ ω * seqDistortion d (V ω) (Y ω))
      ≤ n * (1 / n * ∑ i : Fin n, infoRD p d (Dl i)) := mul_le_mul_of_nonneg_left hJ hn'.le
    _ = ∑ i : Fin n, infoRD p d (Dl i) := by field_simp
    _ ≤ I[V : Y ; μ] := hsum.trans h2

end Block

/-! ### The converse for a single code -/

namespace RDCode

variable {M n : ℕ} {p : α → ℝ} {d : α → β → ℝ}

/-- The reproduction `X̂ⁿ = gₙ(fₙ(Xⁿ))` of a code. -/
def reproduce (c : RDCode M n α β) (x : Fin n → α) : Fin n → β := c.dec (c.enc x)

/-- The expected distortion `E d(Xᵢ, X̂ᵢ)` of the `i`-th letter. -/
def letterDistortion (p : α → ℝ) (d : α → β → ℝ) (c : RDCode M n α β) (i : Fin n) : ℝ :=
  ∑ x, iidPMF p n x * d (x i) (c.reproduce x i)

omit [Fintype β] in
/-- **(10.70)** `E d(Xⁿ, X̂ⁿ) = (1/n) ∑ᵢ E d(Xᵢ, X̂ᵢ)`. -/
lemma distortion_eq_sum (c : RDCode M n α β) :
    c.distortion p d = (∑ i, c.letterDistortion p d i) / n := by
  simp only [distortion, letterDistortion, seqDistortion, reproduce, mul_div_assoc', mul_sum,
    sum_div]
  rw [sum_comm]

omit [Fintype β] in
lemma minDistortion_le_letterDistortion [Finite β] (hp : IsPMF p) (c : RDCode M n α β) (i : Fin n) :
    minDistortion p d ≤ c.letterDistortion p d i := by
  have h := expect_iidPMF_apply hp (fun a => ⨅ y, d a y) i
  simp only [expect] at h
  calc minDistortion p d = ∑ x, iidPMF p n x * ⨅ y, d (x i) y := by
        rw [minDistortion, sum_congr rfl fun a _ => mul_comm (p a) _, ← h]
        exact sum_congr rfl fun x _ => mul_comm _ _
    _ ≤ c.letterDistortion p d i := sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (ciInf_le_distortion d _ _) (iidPMF_nonneg hp.nonneg x)
omit [Fintype β] in
/-- No code has distortion below `D_min`. -/
lemma minDistortion_le_distortion [Finite β] (hp : IsPMF p) (hn : 0 < n) (c : RDCode M n α β) :
    minDistortion p d ≤ c.distortion p d := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [distortion_eq_sum, le_div_iff₀ hn']
  calc minDistortion p d * n = ∑ _i : Fin n, minDistortion p d := by simp [mul_comm]
    _ ≤ ∑ i, c.letterDistortion p d i :=
        sum_le_sum fun i _ => minDistortion_le_letterDistortion hp c i

/-- **(10.58)–(10.71) The converse to the rate distortion theorem.** A `(M, n)` code with
distortion `D` has `log M ≥ n R^(I)(D)`: `log M ≥ H(fₙ(Xⁿ)) ≥ I(Xⁿ; X̂ⁿ) ≥ n R^(I)(D)`. -/
theorem mul_infoRD_le_log [Nonempty β] (hp : IsPMF p) (hn : 0 < n) (c : RDCode M n α β) :
    n * infoRD p d (c.distortion p d) ≤ log M := by
  set μ := iidPMF p n
  have hμ : IsPMF μ := iidPMF_isPMF hp n
  have h := mul_infoRD_le_mutualInfo (d := d) hp hμ hn (dist_id μ) c.reproduce
  calc n * infoRD p d (c.distortion p d) ≤ I[id : c.reproduce ; μ] := h
    _ ≤ H[c.reproduce ; μ] := by
        rw [mutualInfo_eq_entropy_sub_condEntropy' hμ]
        linarith [condEntropy_nonneg hμ c.reproduce id]
    _ ≤ H[c.enc ; μ] := entropyRV_comp_le hμ c.enc c.dec
    _ ≤ log M := by simpa using entropyRV_le_log_card hμ c.enc

end RDCode

/-! ### Achievable pairs -/

variable {p : α → ℝ} {d : α → β → ℝ}

omit [Fintype β] in
/-- An achievable pair has `D ≥ D_min`. -/
theorem IsAchievableRD.minDistortion_le [Finite β] (hp : IsPMF p) {R D : ℝ}
    (h : IsAchievableRD p d R D) :
    minDistortion p d ≤ D := by
  obtain ⟨c, hc⟩ := h
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := ((hc ε hε).and (eventually_gt_atTop 0)).exists
  exact ((c n).minDistortion_le_distortion hp hn.2).trans hn.1

/-- A code with at most `e^{nR}` codewords and distortion `D'` has `R^(I)(D') ≤ R`. -/
lemma RDCode.infoRD_le [Nonempty β] (hp : IsPMF p) {n M : ℕ} (hn : 0 < n) {R : ℝ}
    (hM : (M : ℝ) ≤ exp (n * R)) (c : RDCode M n α β) : infoRD p d (c.distortion p d) ≤ R := by
  have : Nonempty α := by
    obtain ⟨a, -⟩ := Finset.card_pos.1 (card_pos_of_isPMF hp)
    exact ⟨a⟩
  have hM0 : (0 : ℝ) < M := by
    have : 0 < M := Fin.pos (c.enc fun _ => Classical.arbitrary α)
    exact_mod_cast this
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := c.mul_infoRD_le_log (d := d) hp hn
  have hlog : log M ≤ n * R := by
    have := log_le_log hM0 hM
    rwa [log_exp] at this
  nlinarith

/-- **Theorem 10.2.1 (converse).** If `(R, D)` is achievable, then `R ≥ R^(I)(D)`. -/
theorem IsAchievableRD.infoRD_le [Nonempty β] (hp : IsPMF p) {R D : ℝ}
    (h : IsAchievableRD p d R D) : infoRD p d D ≤ R := by
  have hD := h.minDistortion_le hp
  obtain ⟨c, hc⟩ := h
  refine infoRD_le_of_tendsto hp (Dₖ := fun k : ℕ => D + 1 / (k + 1)) (Rₖ := fun _ => R)
    (fun k => by have : (0 : ℝ) < 1 / (k + 1) := by positivity
                 linarith)
    (fun k => ?_) ?_ tendsto_const_nhds
  · obtain ⟨n, hn⟩ := ((hc (1 / (k + 1)) (by positivity)).and (eventually_gt_atTop 0)).exists
    calc infoRD p d (D + 1 / (k + 1)) ≤ infoRD p d ((c n).distortion p d) :=
          infoRD_antitoneOn hp ((c n).minDistortion_le_distortion hp hn.2)
            (show minDistortion p d ≤ D + 1 / (k + 1) by
              have : (0 : ℝ) < 1 / (k + 1) := by positivity
              linarith) hn.1
      _ ≤ R := (c n).infoRD_le hp hn.2 (Nat.floor_le (exp_pos _).le)
  · simpa using (tendsto_const_nhds (x := D)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end InfoTheory
