/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NNCRate
public import InfoTheoryLib.Network.RelayRates

/-!
# The noisy network coding theorems

Theorems 3 and 5 of Lecture 19 of El Gamal and Kim.

## Main statements

* `nnc_wrong_sum_le`: the bound on the expected number of wrong messages that pass the test.
* `isAchievableDMN_nnc`: **Theorem 5 of Lecture 19, the noisy network coding inner bound**, without
  the time sharing random variable.
* `isAchievableMN_nnc`: **Theorem 3 of Lecture 19, the noisy network coding lower bound**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

section Count

variable {N n : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {M K : Fin N → ℕ} [∀ k, NeZero (K k)]
  {px : ∀ k, X k → ℝ} {q : ∀ k, X k → V k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}
  {τ : ∀ k, X k × Y k → V k → ℝ}

open Classical in
/-- The number of tuples of messages with a given set of wrong messages. -/
lemma sum_ind_wrong_le (m : ∀ k, Fin (M k)) (T : Finset (Fin N)) (P : (∀ k, Fin (M k)) → Prop) :
    ∑ m' : ∀ k, Fin (M k), ind (P m' ∧ univ.filter (fun k => m' k ≠ m k) = T) ≤ ∏ k ∈ T, (M k : ℝ)
      := by
  rw [sum_ind_eq_card]
  have hc : ∏ k ∈ T, (M k : ℝ) = (Fintype.card (∀ k : T, Fin (M k)) : ℝ) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Nat.cast_prod, Finset.prod_coe_sort T fun k => (M k : ℝ)]
  rw [hc, ← card_univ]
  norm_cast
  refine card_le_card_of_injOn (fun m' (k : T) => m' k) (fun _ _ => mem_univ _)
    fun a ha b hb hab => ?_
  have ha' : univ.filter (fun k => a k ≠ m k) = T :=
    (by simpa using ha : P a ∧ univ.filter (fun k => a k ≠ m k) = T).2
  have hb' : univ.filter (fun k => b k ≠ m k) = T :=
    (by simpa using hb : P b ∧ univ.filter (fun k => b k ≠ m k) = T).2
  funext k
  by_cases hk : k ∈ T
  · exact congrFun hab ⟨k, hk⟩
  · have h₁ : k ∉ univ.filter (fun k => a k ≠ m k) := by rwa [ha']
    have h₂ : k ∉ univ.filter (fun k => b k ≠ m k) := by rwa [hb']
    simp only [mem_filter, mem_univ, true_and, not_not] at h₁ h₂
    rw [h₁, h₂]

omit [∀ k, NeZero (K k)] in
/-- A product of bounds. -/
lemma prod_le_two_pow_mul_exp (A : Finset (Fin N)) {r : Fin N → ℝ}
    (hK : ∀ k, (K k : ℝ) ≤ 2 * exp (n * r k)) :
    ∏ k ∈ A, (K k : ℝ) ≤ 2 ^ N * exp (n * ∑ k ∈ A, r k) := by
  calc _ ≤ ∏ k ∈ A, (2 * exp (n * r k)) :=
        prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) fun k _ => hK k
    _ = 2 ^ A.card * exp (n * ∑ k ∈ A, r k) := by
        rw [prod_mul_distrib, prod_const, mul_sum, exp_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
        refine pow_le_pow_right₀ (by norm_num) ?_
        simpa using card_le_univ A

/-- **The expected number of wrong messages that pass the test.** -/
theorem nnc_wrong_sum_le (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W) (hτ : ∀ k, IsChannel (τ k))
    (hq : ∀ k a b, nncRho (nncLaw px W τ) k (a, b) =
      dist (nncLaw px W τ) (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b)
    (hqc : ∀ k, IsChannel (q k)) (d : Fin N) (ε : ℝ)
    (pk : ∀ k, (Fin n → X k) → (Fin (K k) → Fin n → V k) → (Fin n → Y k) → Fin (K k))
    (dξ : NNCΞ M K n X Y V) (s : ℕ) {R r a : Fin N → ℝ} {ζ : ℝ} (hR0 : ∀ k, 0 ≤ R k)
    (hK : ∀ k, (K k : ℝ) ≤ 2 * exp (n * r k)) (ha : ∀ k, 0 ≤ a k)
    (hM : ∀ k, (M k : ℝ) ≤ exp (n * ((s + 1) * (R k * log 2)) + a k))
    (hMR : ∀ k, 2 ≤ M k → 0 < R k)
    (hslack : ∀ A : Finset (Fin N), d ∉ A → (∃ k ∈ A, 0 < R k) →
      (∑ k ∈ A, R k) * log 2 + ζ + ∑ k ∈ A, r k ≤
        nncJ (nncLaw px W τ) A d - ε * nncC (nncLaw px W τ) A d)
    (m : ∀ k, Fin (M k)) :
    ∑ m' : ∀ k, Fin (M k), ind (m' ≠ m ∧ m' d = m d) *
        nncCount (nncLaw px W τ) px q W d ε pk m m' dξ (s + 1) 0 0 ≤
      2 ^ N * (exp (∑ k, a k) * ((2 ^ N * (2 ^ N * 2 ^ N) ^ s * (2 ^ N * 2 ^ N)) *
        exp (-(n * ((s + 1) * ζ - ∑ k, r k))))) := by
  classical
  set L := nncLaw (V := V) px W τ with hL
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  set c₂ : ℝ := 2 ^ N * (2 ^ N * 2 ^ N) ^ s * (2 ^ N * 2 ^ N) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the bound for a set of wrong messages
  let f : Finset (Fin N) → ℝ := fun T =>
    c₂ * (exp (-(n * ((∑ k ∈ T, R k) * log 2 + ζ))) ^ (s + 1) * exp (n * ∑ k, r k))
  have hf0 : ∀ T, 0 ≤ f T := fun T => by positivity
  have hcount : ∀ m' : ∀ k, Fin (M k), m' ≠ m → m' d = m d →
      nncCount L px q W d ε pk m m' dξ (s + 1) 0 0 ≤ f (univ.filter fun k => m' k ≠ m k) := by
    intro m' hne hd
    set T := univ.filter fun k => m' k ≠ m k with hT
    set g := exp (-(n * ((∑ k ∈ T, R k) * log 2 + ζ))) with hg
    have hg0 : 0 ≤ g := (exp_pos _).le
    have hγ : ∀ A ∈ nncAdm m m' d, nncE L n d ε A * ∏ k ∈ A, (K k : ℝ) ≤ 2 ^ N * g := by
      intro A hA
      obtain ⟨hdA, hTA⟩ := (mem_filter.mp hA).2
      obtain ⟨k₀, hk₀⟩ : ∃ k, m' k ≠ m k := Function.ne_iff.mp hne
      have hk₀T : k₀ ∈ T := mem_filter.mpr ⟨mem_univ _, hk₀⟩
      have hposR : 0 < R k₀ := by
        refine hMR k₀ ?_
        by_contra hlt
        have h1 : M k₀ ≤ 1 := by omega
        have := (m' k₀).2
        have := (m k₀).2
        exact hk₀ (Fin.ext (by omega))
      have hsl := hslack A hdA ⟨k₀, hTA hk₀T, hposR⟩
      have hRT : ∑ k ∈ T, R k ≤ ∑ k ∈ A, R k :=
        sum_le_sum_of_subset_of_nonneg hTA fun k _ _ => hR0 k
      have hprod := prod_le_two_pow_mul_exp (n := n) A hK
      calc _ ≤ nncE L n d ε A * (2 ^ N * exp (n * ∑ k ∈ A, r k)) :=
            mul_le_mul_of_nonneg_left hprod (nncE_pos _ _ _ _ _).le
        _ = 2 ^ N * (nncE L n d ε A * exp (n * ∑ k ∈ A, r k)) := by ring
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [nncE, ← exp_add, hg]
            refine exp_le_exp.mpr ?_
            have h₁ : (∑ k ∈ T, R k) * log 2 ≤ (∑ k ∈ A, R k) * log 2 :=
              mul_le_mul_of_nonneg_right hRT hlog.le
            nlinarith
    have hγ0 : (0 : ℝ) ≤ 2 ^ N * g := by positivity
    have hc := nnc_pathCount_le hpx hW hτ hq hqc d ε pk hd dξ hγ0 hγ s 0 0
    have hS : nncS m m' (0 : ∀ k, Fin (K k)) 0 = T := by
      ext k
      simp [nncS, hT]
    rw [hS] at hc
    have hTA : T ∈ nncAdm m m' d := by
      refine mem_filter.mpr ⟨mem_univ _, ?_, subset_rfl⟩
      simp [hT, hd]
    have hprodT : (1 : ℝ) ≤ ∏ k ∈ T, (K k : ℝ) := by
      have : 1 ≤ ∏ k ∈ T, K k := Finset.one_le_prod fun k _ => NeZero.pos (K k)
      exact_mod_cast this
    have hE : nncE L n d ε T ≤ 2 ^ N * g := by
      refine le_trans ?_ (hγ T hTA)
      exact le_mul_of_one_le_right (nncE_pos _ _ _ _ _).le hprodT
    have hK₀ := prod_le_two_pow_mul_exp (n := n) (univ : Finset (Fin N)) hK
    refine hc.trans ?_
    have hP0 : 0 ≤ (2 ^ N * (2 ^ N * g)) ^ s * (2 ^ N * ∏ k, (K k : ℝ)) := by
      have : 0 ≤ ∏ k, (K k : ℝ) := prod_nonneg fun k _ => Nat.cast_nonneg _
      positivity
    calc _ ≤ 2 ^ N * g * ((2 ^ N * (2 ^ N * g)) ^ s * (2 ^ N * ∏ k, (K k : ℝ))) :=
          mul_le_mul_of_nonneg_right hE hP0
      _ ≤ 2 ^ N * g * ((2 ^ N * (2 ^ N * g)) ^ s * (2 ^ N * (2 ^ N * exp (n * ∑ k, r k)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hK₀ (by positivity)) (by positivity)) (by positivity)
      _ = _ := by
          simp only [f, hc₂]
          ring
  -- the sum over the sets of wrong messages
  have hsets : ∀ T : Finset (Fin N), (∏ k ∈ T, (M k : ℝ)) * f T ≤
      exp (∑ k, a k) * (c₂ * exp (-(n * ((s + 1) * ζ - ∑ k, r k)))) := by
    intro T
    have hp : ∏ k ∈ T, (M k : ℝ) ≤ exp (n * ((s + 1) * ((∑ k ∈ T, R k) * log 2))) *
        exp (∑ k, a k) := by
      calc _ ≤ ∏ k ∈ T, exp (n * ((s + 1) * (R k * log 2)) + a k) :=
            prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) fun k _ => hM k
        _ = exp (n * ((s + 1) * ((∑ k ∈ T, R k) * log 2))) * exp (∑ k ∈ T, a k) := by
            rw [← exp_sum, sum_add_distrib, exp_add, sum_mul, mul_sum, mul_sum]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (exp_pos _).le
            exact sum_le_sum_of_subset_of_nonneg (subset_univ T) fun k _ _ => ha k
    calc _ ≤ exp (n * ((s + 1) * ((∑ k ∈ T, R k) * log 2))) * exp (∑ k, a k) * f T :=
          mul_le_mul_of_nonneg_right hp (hf0 T)
      _ = _ := by
          simp only [f]
          rw [← exp_nat_mul]
          have : exp (n * ((s + 1) * ((∑ k ∈ T, R k) * log 2))) * exp (∑ k, a k) *
              (c₂ * (exp (((s + 1 : ℕ) : ℝ) * -(n * ((∑ k ∈ T, R k) * log 2 + ζ))) *
                exp (n * ∑ k, r k))) = exp (∑ k, a k) * (c₂ *
              (exp (n * ((s + 1) * ((∑ k ∈ T, R k) * log 2))) *
                exp (((s + 1 : ℕ) : ℝ) * -(n * ((∑ k ∈ T, R k) * log 2 + ζ))) *
                exp (n * ∑ k, r k))) := by ring
          rw [this, ← exp_add, ← exp_add]
          congr 3
          push_cast
          ring
  calc _ ≤ ∑ m' : ∀ k, Fin (M k), ind (m' ≠ m ∧ m' d = m d) *
        f (univ.filter fun k => m' k ≠ m k) := by
        refine sum_le_sum fun m' _ => ?_
        by_cases h : m' ≠ m ∧ m' d = m d
        · rw [ind_of_pos h, one_mul, one_mul]
          exact hcount m' h.1 h.2
        · rw [ind_of_neg h, zero_mul, zero_mul]
    _ = ∑ T : Finset (Fin N), f T * ∑ m' : ∀ k, Fin (M k), ind ((m' ≠ m ∧ m' d = m d) ∧
          univ.filter (fun k => m' k ≠ m k) = T) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun m' _ => ?_
        rw [Finset.sum_eq_single (univ.filter fun k => m' k ≠ m k)]
        · by_cases h : m' ≠ m ∧ m' d = m d
          · rw [ind_of_pos h, ind_of_pos ⟨h, rfl⟩]
            ring
          · rw [ind_of_neg h, ind_of_neg fun h' => h h'.1]
            ring
        · intro T _ hT
          rw [ind_of_neg fun h' => hT h'.2.symm, mul_zero]
        · simp
    _ ≤ ∑ T : Finset (Fin N), (∏ k ∈ T, (M k : ℝ)) * f T := by
        refine sum_le_sum fun T _ => ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (sum_ind_wrong_le m T _) (hf0 T)
    _ ≤ ∑ _T : Finset (Fin N), exp (∑ k, a k) * (c₂ * exp (-(n * ((s + 1) * ζ - ∑ k, r k)))) :=
        sum_le_sum fun T _ => hsets T
    _ = _ := by
        rw [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rfl

end Count

/-! ### The coding theorems -/

section Theorems

variable {N : ℕ} {X Y V : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  [∀ k, Fintype (V k)] {px : ∀ k, X k → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}
  {τ : ∀ k, X k × Y k → V k → ℝ}

/-- A joint law is a marginal law and a channel. -/
lemma exists_channel_of_joint {α β : Type*} [Fintype α] [Fintype β] [Nonempty β] {J : α × β → ℝ}
    (hJ : IsPMF J) : ∃ K : α → β → ℝ, IsChannel K ∧ ∀ a b, J (a, b) = marg J a * K a b := by
  classical
  let K : α → β → ℝ := fun a => if marg J a = 0 then uniformPMF β else condPMF J a
  refine ⟨K, fun a => ?_, fun a b => ?_⟩
  · by_cases h : marg J a = 0
    · simp only [K, h, ite_true]
      exact uniformPMF_isPMF
    · simp only [K, h, ite_false]
      exact condPMF_isPMF hJ.nonneg h
  · by_cases h : marg J a = 0
    · rw [h, zero_mul]
      have h₁ := le_marg hJ.nonneg a b
      rw [h] at h₁
      exact le_antisymm h₁ (hJ.nonneg _)
    · simp only [K, h, ite_false, condPMF]
      field_simp

/-- A positive function on a finite type is bounded below by a positive number. -/
lemma exists_pos_le_of_finite {ι : Type*} [Finite ι] {g : ι → ℝ} (hg : ∀ i, 0 < g i) :
    ∃ ξ > 0, ∀ i, ξ ≤ g i := by
  have := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (univ : Finset ι) g univ_nonempty
    exact ⟨g i₀, hg i₀, fun i => hi₀ i (mem_univ i)⟩

/-- **Theorem 5 of Lecture 19 of [elgamal2010], page 19-40: the noisy network coding inner bound**,
without the time sharing variable. If `∑_{k ∈ S} R_k < I(X(S); Ŷ(Sᶜ), Y_d | X(Sᶜ)) -
I(Y(S); Ŷ(S) | Xᴺ, Ŷ(Sᶜ),
Y_d)` for all the destinations `d` and all the cuts `S` that do not contain `d`, then the rates are
achievable. The cuts in which all the rates are zero are not needed: no message of such a cut can be
wrong. All the destinations decode all the messages. -/
theorem isAchievableDMN_nnc (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W)
    (hτ : ∀ k, IsChannel (τ k)) {D : Fin N → Finset (Fin N)} {R : Fin N → ℝ} (hR0 : ∀ k, 0 ≤ R k)
    (hrate : ∀ d ∈ univ.biUnion D, ∀ S : Finset (Fin N), d ∉ S → (∃ k ∈ S, 0 < R k) →
      (∑ k ∈ S, R k) * log 2 < nncInfo (nncLaw px W τ) S d) :
    IsAchievableDMN W D R := by
  classical
  have hL := nncLaw_isPMF hpx hW hτ (V := V)
  set L := nncLaw (V := V) px W τ with hLd
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  -- the alphabets are not empty
  have hΩ : Nonempty (NNCΩ X Y V) := Fintype.card_pos_iff.mp (card_pos_of_isPMF hL)
  obtain ⟨x₀, y₀, v₀⟩ := hΩ
  -- the channels of the descriptions
  have hqex : ∀ k, ∃ K : X k → V k → ℝ, IsChannel K ∧
      ∀ a b, nncRho L k (a, b) = marg (nncRho L k) a * K a b := fun k => by
    have : Nonempty (V k) := ⟨v₀ k⟩
    exact exists_channel_of_joint (hL.dist _)
  choose q hqc hq₀ using hqex
  have hq : ∀ k a b, nncRho L k (a, b) =
      dist L (fun ω : NNCΩ X Y V => ω.1 k) a * q k a b := by
    intro k a b
    have hm : marg (nncRho L k) a = dist L (fun ω : NNCΩ X Y V => ω.1 k) a := by
      rw [marg_eq_dist, nncRho, ← dist_dist_comp]
      rfl
    rw [hq₀, hm]
  -- the slack in the rates
  obtain ⟨ξ, hξ, hslack₀⟩ := exists_pos_le_of_finite (ι := Finset (Fin N) × Fin N)
    (g := fun x => if x.2 ∈ univ.biUnion D ∧ x.2 ∉ x.1 ∧ ∃ k ∈ x.1, 0 < R k then
      nncInfo L x.1 x.2 - (∑ k ∈ x.1, R k) * log 2 else 1) (fun x => by
      split_ifs with h
      · have := hrate x.2 h.1 x.1 h.2.1 h.2.2
        linarith
      · exact one_pos)
  have hslack₁ : ∀ d ∈ univ.biUnion D, ∀ S : Finset (Fin N), d ∉ S → (∃ k ∈ S, 0 < R k) →
      (∑ k ∈ S, R k) * log 2 + ξ ≤ nncInfo L S d := by
    intro d hd S hdS hS
    have := hslack₀ (S, d)
    simp only [hd, hdS, hS, not_false_eq_true, and_self, ite_true] at this
    linarith
  -- the parameters
  set ϑ := ξ / (6 * ((N : ℝ) + 1)) with hϑd
  have hϑ : 0 < ϑ := by positivity
  set r : Fin N → ℝ := fun k => nncI L k + 2 * ϑ with hr
  have hI0 : ∀ k, 0 ≤ nncI L k := nncI_nonneg hL
  have hr0 : ∀ k, 0 ≤ r k := fun k => by
    have := hI0 k
    simp only [hr]
    linarith
  set Cmax := ∑ S : Finset (Fin N), ∑ d : Fin N, |nncC L S d| with hCmax
  have hCm0 : 0 ≤ Cmax := sum_nonneg fun S _ => sum_nonneg fun d _ => abs_nonneg _
  have hCle : ∀ S d, nncC L S d ≤ Cmax := by
    intro S d
    refine (le_abs_self _).trans ?_
    refine le_trans ?_ (single_le_sum (f := fun S => ∑ d : Fin N, |nncC L S d|)
      (fun S _ => sum_nonneg fun d _ => abs_nonneg _) (mem_univ S))
    exact single_le_sum (f := fun d => |nncC L S d|) (fun d _ => abs_nonneg _) (mem_univ d)
  set ε := ξ / (3 * (Cmax + 1)) with hεd
  have hε : 0 < ε := by positivity
  have hεC : ∀ S d, ε * nncC L S d ≤ ξ / 3 := by
    intro S d
    calc ε * nncC L S d ≤ ε * Cmax := mul_le_mul_of_nonneg_left (hCle S d) hε.le
      _ ≤ ε * (Cmax + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = ξ / 3 := by
          rw [hεd]
          field_simp
  set ζ := ξ / 3 with hζ
  have hζ0 : 0 < ζ := by positivity
  have hslack : ∀ d ∈ univ.biUnion D, ∀ A : Finset (Fin N), d ∉ A → (∃ k ∈ A, 0 < R k) →
      (∑ k ∈ A, R k) * log 2 + ζ + ∑ k ∈ A, r k ≤ nncJ L A d - ε * nncC L A d := by
    intro d hd A hdA hA
    have h₁ := hslack₁ d hd A hdA hA
    have h₂ := nncInfo_le hL A d
    have h₃ := hεC A d
    have h₄ : ∑ k ∈ A, r k ≤ ∑ k ∈ A, nncI L k + ξ / 3 := by
      simp only [hr]
      rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      have hcard : (A.card : ℝ) ≤ N := by
        have := card_le_univ A
        simp only [Fintype.card_fin] at this
        exact_mod_cast this
      have : (A.card : ℝ) * (2 * ϑ) ≤ ξ / 3 := by
        rw [hϑd]
        have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        calc (A.card : ℝ) * (2 * (ξ / (6 * ((N : ℝ) + 1))))
            = (A.card : ℝ) / ((N : ℝ) + 1) * (ξ / 3) := by
              field_simp
              ring
          _ ≤ 1 * (ξ / 3) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [div_le_one hN]
              linarith
          _ = ξ / 3 := one_mul _
      linarith
    linarith
  -- the number of blocks
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ∑ k, r k + 1 ≤ ((s : ℝ) + 1) * ζ := by
    obtain ⟨s, hs⟩ := exists_nat_ge ((∑ k, r k + 1) / ζ)
    refine ⟨s, ?_⟩
    rw [div_le_iff₀ hζ0] at hs
    nlinarith
  set a : Fin N → ℝ := fun k => log 2 * (((s : ℝ) + 1) * R k + 1) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    have := hR0 k
    simp only [ha]
    positivity
  -- the sizes of the codebooks
  let K : ℕ → Fin N → ℕ := fun n k => ⌈exp (n * r k)⌉₊
  have hK0 : ∀ n k, NeZero (K n k) := fun n k => ⟨(Nat.ceil_pos.mpr (exp_pos _)).ne'⟩
  have hKge : ∀ᶠ n : ℕ in atTop, ∀ k, exp (n * (nncI L k + ϑ)) ≤ K n k := by
    refine Eventually.of_forall fun n k => ?_
    refine le_trans (exp_le_exp.mpr ?_) (Nat.le_ceil _)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [hr]
    nlinarith
  have hKle : ∀ n k, (K n k : ℝ) ≤ 2 * exp (n * r k) := by
    intro n k
    have h₁ : 1 ≤ exp ((n : ℝ) * r k) :=
      one_le_exp (mul_nonneg (Nat.cast_nonneg n) (hr0 k))
    have h₂ := Nat.ceil_lt_add_one (exp_pos ((n : ℝ) * r k)).le
    simp only [K]
    linarith
  -- the error for each length
  have hdef : ∀ N' : ℕ, Nonempty (DMNCode (fun k => 2 ^ ⌈(N' : ℝ) * R k⌉₊) N' X Y) := fun N' =>
    ⟨⟨fun k _ _ _ => x₀ k, fun _ _ _ j => ⟨0, by positivity⟩⟩⟩
  have hsmall : ∀ η > 0, ∀ᶠ N' : ℕ in atTop, ∃ c : DMNCode (fun k => 2 ^ ⌈(N' : ℝ) * R k⌉₊) N' X Y,
      c.errProb W D ≤ η := by
    intro η hη
    set t := s + 1 with ht
    have htpos : (0 : ℝ) < t := by positivity
    set cc : ℝ := 2 ^ N * (exp (∑ k, a k) * ((2 ^ N * (2 ^ N * 2 ^ N) ^ s * (2 ^ N * 2 ^ N)))) with
      hcc
    have hcc0 : 0 ≤ cc := by positivity
    set cD : ℝ := ((univ.biUnion D).card : ℝ) with hcD
    have hcD0 : 0 ≤ cD := Nat.cast_nonneg _
    have hexp : Tendsto (fun n : ℕ => exp (-(n : ℝ))) atTop (𝓝 0) :=
      tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
    have htail : ∀ᶠ n : ℕ in atTop, cD * (cc * exp (-(n : ℝ))) ≤ η / 2 := by
      have h₁ : Tendsto (fun n : ℕ => cD * (cc * exp (-(n : ℝ)))) atTop (𝓝 (cD * (cc * 0))) :=
        (hexp.const_mul cc).const_mul cD
      simp only [mul_zero] at h₁
      filter_upwards [(tendsto_order.1 h₁).2 (η / 2) (by positivity)] with n hn using hn.le
    have hcover := nnc_cover hpx hW hτ hq hqc hε (K := K) hϑ hKge
      (η := η / (2 * t)) (by positivity)
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hcover.and (htail.and (eventually_gt_atTop 0)))
    refine eventually_atTop.mpr ⟨t * n₀ + t, fun N' hN' => ?_⟩
    set n := N' / t with hn
    have hnge : n₀ ≤ n := by
      rw [hn, Nat.le_div_iff_mul_le (by positivity)]
      calc n₀ * t = t * n₀ := Nat.mul_comm _ _
        _ ≤ N' := by omega
    obtain ⟨⟨pk, hpk⟩, htailn, hnpos⟩ := hn₀ n hnge
    have : NeZero n := ⟨hnpos.ne'⟩
    have : ∀ k, NeZero (K n k) := hK0 n
    have htn : t * n ≤ N' := by
      rw [hn]
      exact Nat.mul_div_le N' t
    have hNlt : (N' : ℝ) < t * ((n : ℝ) + 1) := by
      have h₁ : N' < t * (n + 1) := by
        rw [hn]
        exact Nat.lt_mul_div_succ N' (by positivity)
      exact_mod_cast h₁
    set M : Fin N → ℕ := fun k => 2 ^ ⌈(N' : ℝ) * R k⌉₊ with hMd
    have hMpos : ∀ k, 0 < M k := fun k => by
      simp only [hMd]
      positivity
    have hMle : ∀ k, (M k : ℝ) ≤ exp (n * (((s : ℝ) + 1) * (R k * log 2)) + a k) := by
      intro k
      have hN0 : (0 : ℝ) ≤ (N' : ℝ) * R k := mul_nonneg (Nat.cast_nonneg _) (hR0 k)
      have h₁ := (Nat.ceil_lt_add_one hN0).le
      have h₂ : (M k : ℝ) = exp ((⌈(N' : ℝ) * R k⌉₊ : ℝ) * log 2) := by
        simp only [hMd]
        push_cast
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
      rw [h₂]
      refine exp_le_exp.mpr ?_
      have h₃ : (N' : ℝ) * R k ≤ t * ((n : ℝ) + 1) * R k :=
        mul_le_mul_of_nonneg_right hNlt.le (hR0 k)
      have h₄ : ((t : ℕ) : ℝ) = (s : ℝ) + 1 := by
        rw [ht]
        push_cast
        ring
      rw [h₄] at h₃
      simp only [ha]
      nlinarith
    have hMR : ∀ k, 2 ≤ M k → 0 < R k := by
      intro k hk
      refine lt_of_le_of_ne (hR0 k) fun h0 => ?_
      simp only [hMd, ← h0, mul_zero, Nat.ceil_zero, pow_zero] at hk
      omega
    let dξ : NNCΞ M (K n) n X Y V :=
      (fun k _ => (fun _ => x₀ k, fun _ _ => v₀ k), fun _ => y₀)
    have hη' : ∀ (m : ∀ k, Fin (M k)) (a : ∀ k, Fin (K n k)), ∑ ξ' : NNCΞ M (K n) n X Y V,
        nncP px q W m a ξ' * ind (nncBad L ε (nncX ξ'.1 (nncBr m a)) ξ'.2
          (nncVOf ξ'.1 (nncBr m a) pk ξ'.2)) ≤ η / (2 * t) := by
      intro m a
      rw [nnc_true_le hpx hqc pk m a]
      exact hpk
    have hβ : ∀ (m : ∀ k, Fin (M k)), ∀ d ∈ univ.biUnion D, ∑ m' : ∀ k, Fin (M k),
        ind (m' ≠ m ∧ m' d = m d) * nncCount L px q W d ε pk m m' dξ t 0 0 ≤
          cc * exp (-(n : ℝ)) := by
      intro m d hd
      have h₁ := nnc_wrong_sum_le hpx hW hτ hq hqc d ε pk dξ s hR0 (hKle n) ha0 hMle hMR
        (hslack d hd) m
      refine h₁.trans ?_
      have h₂ : exp (-((n : ℝ) * (((s : ℝ) + 1) * ζ - ∑ k, r k))) ≤ exp (-(n : ℝ)) := by
        refine exp_le_exp.mpr ?_
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      calc _ ≤ 2 ^ N * (exp (∑ k, a k) * ((2 ^ N * (2 ^ N * 2 ^ N) ^ s * (2 ^ N * 2 ^ N)) *
            exp (-(n : ℝ)))) := by
            gcongr
        _ = _ := by
            simp only [hcc]
            ring
    obtain ⟨c, hc⟩ := nnc_exists_code (t := t) L hpx hqc hW ε pk dξ y₀ hMpos D
      (β := cc * exp (-(n : ℝ))) hη' hβ htn
    refine ⟨c, hc.trans ?_⟩
    have h₁ : (t : ℝ) * (η / (2 * t)) = η / 2 := by
      field_simp
    rw [h₁]
    linarith
  obtain ⟨c, hc⟩ := exists_seq_tendsto (C := fun N' : ℕ => DMNCode (fun k => 2 ^ ⌈(N' : ℝ) * R k⌉₊)
    N' X Y) (fun N' c => c.errProb W D) (fun N' c => by
      have hμ := c.law_isPMF (fun k => by positivity) hW
      exact sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (ind_nonneg _)) hsmall
  exact ⟨c, hc⟩

/-- **Theorem 3 of Lecture 19 of [elgamal2010], page 19-18: the noisy network coding lower bound.**
For independent inputs and compressions `p(x_k) p(ŷ_k | y_k, x_k)`, the rate `R` is achievable if
`R < I(X(S); Ŷ(Sᶜ), Y_d | X(Sᶜ)) - I(Y(S); Ŷ(S) | Xᴺ, Ŷ(Sᶜ), Y_d)` for all the destinations `d` and
all the cuts `S` with `s ∈ S` and `d ∉ S`. -/
theorem isAchievableMN_nnc (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W)
    (hτ : ∀ k, IsChannel (τ k)) {s : Fin N} {D : Finset (Fin N)} {R : ℝ} (hR : 0 ≤ R)
    (hrate : ∀ d ∈ D, ∀ S : Finset (Fin N), s ∈ S → d ∉ S →
      R * log 2 < nncInfo (nncLaw px W τ) S d) :
    IsAchievableMN W s D R := by
  classical
  refine isAchievableDMN_nnc hpx hW hτ (fun k => ?_) fun d hd S hdS hS => ?_
  · simp only [mcRate]
    split_ifs
    · exact hR
    · exact le_rfl
  · obtain ⟨j, -, hj⟩ := mem_biUnion.mp hd
    have hjs : j = s := by
      by_contra h
      simp [mcDest, h] at hj
    subst hjs
    have hdD : d ∈ D := by simpa [mcDest] using hj
    obtain ⟨k, hk, hkR⟩ := hS
    have hks : k = j := by
      by_contra h
      simp [mcRate, h] at hkR
    subst hks
    have hsum : ∑ i ∈ S, mcRate k R i = R := by
      rw [sum_eq_single k]
      · simp [mcRate]
      · intro i _ hi
        simp [mcRate, hi]
      · exact fun h => absurd hk h
    rw [hsum]
    exact hrate d hdD S hk hdS

omit [∀ k, Fintype (X k)] in
/-- The achievable rates of a multicast network are bounded, if the source has a destination other
than itself. -/
lemma bddAbove_isAchievableMN [∀ k, Finite (X k)] (hW : IsChannel W) {s k : Fin N}
    {D : Finset (Fin N)} (hk : k ∈ D) (hsk : s ≠ k) : BddAbove {R | IsAchievableMN W s D R} := by
  have : ∀ k, Fintype (X k) := fun k => Fintype.ofFinite _
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  refine ⟨log (Fintype.card (∀ j : (({s} : Finset (Fin N))ᶜ : Finset (Fin N)), Y j)) / log 2, ?_⟩
  intro R hR
  obtain ⟨p, hp, hle⟩ := IsAchievableMN.exists_cutset hW hR
  rw [le_div_iff₀ hlog]
  exact (hle k hk {s} (mem_singleton_self s) (by simpa using hsk.symm)).trans
    (cutInfo_le_log_card hp hW _)

/-- **Theorem 3 of Lecture 19 of [elgamal2010], page 19-18**, as a lower bound on the capacity. -/
theorem le_mnCapacity_of_nnc (hpx : ∀ k, IsPMF (px k)) (hW : IsChannel W)
    (hτ : ∀ k, IsChannel (τ k)) {s k : Fin N} {D : Finset (Fin N)} (hk : k ∈ D) (hsk : s ≠ k) {R :
      ℝ}
    (hR : 0 ≤ R) (hrate : ∀ d ∈ D, ∀ S : Finset (Fin N), s ∈ S → d ∉ S →
      R * log 2 < nncInfo (nncLaw px W τ) S d) : R ≤ mnCapacity W s D :=
  le_csSup (bddAbove_isAchievableMN hW hk hsk) (isAchievableMN_nnc hpx hW hτ hR hrate)

end Theorems

end InfoTheory
