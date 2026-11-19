/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.MDNetwork

/-!
# Multiple description networks: the line network

Theorem 1 of Lecture 21 of El Gamal and Kim for the line network: the source is at the node `0` and
the edges go from the node `k` to the node `k + 1`. The node `k` must know the descriptions
of all the nodes from `k` on.

The covering codes are built one layer at a time, from the last node to the first one. Each codeword
of a layer is drawn given the codewords of the later nodes, by the choice of `exists_layer`. The
state of the construction is one tuple with an index for each node, in which the layers that have
not been chosen hold `0`. This avoids dependent types for the index sets.

## Main definitions

* `tailOf k z`: the letters of the nodes from `k` on, the others being replaced by a default value.
* `LineCov`: the covering property of the layers from `k` on.
* `lineEdges`, `linePar`: the line network.

## Main statements

* `lineCov_of_rates`: the layered covering.
* `isAchievableMDN_line`: achievability.
* `mdnRegion_line_eq`: **Theorem 1 for the line network**.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 21
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

variable {N : ℕ} {α : Type*} {β : Fin N → Type*} [Fintype α] [∀ l, Fintype (β l)]
  [∀ l, Nonempty (β l)]

/-! ### Tails of letters and of indices -/

section Tail

open Classical in
/-- The letters of the nodes from `k` on; the other letters are replaced by a default value. -/
def tailOf (k : ℕ) (z : ∀ l, β l) : ∀ l, β l :=
  fun l => if k ≤ (l : ℕ) then z l else Classical.arbitrary _

omit [Fintype α] [∀ l, Fintype (β l)] in
/-- Adding the letter of the node `k` to the tail after `k`. -/
lemma update_tailOf (k : Fin N) (z : ∀ l, β l) :
    Function.update (tailOf (k + 1 : ℕ) z) k (z k) = tailOf k z := by
  classical
  funext l
  by_cases hl : l = k
  · subst hl
    simp [tailOf]
  · have : ((k : ℕ) + 1 ≤ l) ↔ ((k : ℕ) ≤ l) := by
      have : (l : ℕ) ≠ k := fun h => hl (Fin.ext h)
      omega
    simp [tailOf, hl, this]

variable (L : Fin N → ℕ) [∀ l, NeZero (L l)]

/-- The indices of the nodes from `k` on; the other indices are replaced by `0`. -/
def tailIdx (k : ℕ) (t : ∀ l, Fin (L l)) : ∀ l, Fin (L l) :=
  fun l => if k ≤ (l : ℕ) then t l else 0

end Tail

/-! ### The layered covering -/

section Cover

variable {μ : (α × ∀ l, β l) → ℝ}

open Classical in
/-- **The covering property of the layers from `k` on**, with `L n l` indices at the node `l`. For
every `ε` and `η` and all large `n`, there are an encoder with an index for each layer from `k` on,
and codewords of each node that depend on the indices of this node and of the later ones,
such that the source sequence is jointly typical with the codewords, except with probability `η`. -/
def LineCov (μ : (α × ∀ l, β l) → ℝ) (L : ℕ → Fin N → ℕ) [∀ n l, NeZero (L n l)] (k : ℕ) : Prop :=
  ∀ ε > 0, ∀ η > 0, ∀ᶠ n : ℕ in atTop, ∃ (e : (Fin n → α) → ∀ l, Fin (L n l))
    (C : ∀ l, (∀ l', Fin (L n l')) → Fin n → β l),
    (∀ x (l : Fin N), (l : ℕ) < k → e x l = 0) ∧ (∀ (l : Fin N) t t', (∀ i, l ≤ i → t i = t' i) → C
      l t = C l t') ∧
    ∑ x, iidPMF (dist μ Prod.fst) n x *
      (if zipSeq (fun i => tailOf k fun l => C l (e x) i) x ∈
        robustTypicalSet (dist μ (pair (fun z : α × ∀ l, β l => tailOf k z.2) Prod.fst)) n ε
        then 0 else 1) ≤ η

/-- Typical sequences for a smaller parameter are typical. -/
lemma robustTypicalSet_mono {γ : Type*} [Fintype γ] {p : γ → ℝ} (hp : ∀ a, 0 ≤ p a) {n : ℕ}
    {ε ε' : ℝ} (h : ε ≤ ε') : robustTypicalSet p n ε ⊆ robustTypicalSet p n ε' := fun _ hx =>
  mem_robustTypicalSet.2 fun a =>
    (mem_robustTypicalSet.1 hx a).trans (mul_le_mul_of_nonneg_right h (hp a))

variable {L : ℕ → Fin N → ℕ} [∀ n l, NeZero (L n l)]

open Classical in
/-- The last step: no layer has been chosen. -/
lemma lineCov_top (hμ : IsPMF μ) : LineCov μ L N := by
  intro ε hε η hη
  set P := dist μ (Prod.fst : (α × ∀ l, β l) → α) with hP
  have hPp : IsPMF P := hμ.dist _
  have hlim := tendsto_prob_robustTypicalSet hPp hε
  have ht : Tendsto (fun n => 1 - prob (iidPMF P n) (robustTypicalSet P n ε)) atTop (𝓝 0) := by
    simpa using hlim.const_sub 1
  filter_upwards [(tendsto_order.1 ht).2 η hη] with n hn
  refine ⟨fun _ _ => 0, fun l _ _ => Classical.arbitrary _, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, ?_⟩
  set d : ∀ l, β l := fun _ => Classical.arbitrary _ with hd
  have htail : ∀ z : ∀ l, β l, tailOf N z = d := fun z => by
    funext l
    have : ¬ (N ≤ (l : ℕ)) := not_le.2 l.isLt
    simp [tailOf, this, hd]
  have hdist : dist μ (pair (fun z : α × ∀ l, β l => tailOf N z.2) Prod.fst) =
      dist P (fun a => (d, a)) := by
    rw [hP, ← dist_comp_eq]
    congr 1
    funext z
    simp [pair, htail]
  have hμn := iidPMF_isPMF hPp n
  have hpt : ∀ (x : Fin n → α) (w : Fin n → ∀ l, β l), (if zipSeq (fun i => tailOf N (w i)) x ∈
      robustTypicalSet (dist μ (pair (fun z : α × ∀ l, β l => tailOf N z.2) Prod.fst)) n ε
      then (0 : ℝ) else 1) ≤ if x ∈ robustTypicalSet P n ε then 0 else 1 := fun x w => by
    by_cases hx : x ∈ robustTypicalSet P n ε
    · have h₁ := comp_mem_robustTypicalSet hx fun a => (d, a)
      have e : (fun a => (d, a)) ∘ x = zipSeq (fun i => tailOf N (w i)) x := by
        funext i
        simp [zipSeq, htail]
      rw [e, ← hdist] at h₁
      simp [hx, h₁]
    · simp only [hx, ite_false]
      split_ifs <;> norm_num
  refine (sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x _) (hμn.nonneg x)).trans
    (le_trans (le_of_eq ?_) hn.le)
  have h2 : prob (iidPMF P n) (robustTypicalSet P n ε) =
      ∑ x, if x ∈ robustTypicalSet P n ε then iidPMF P n x else 0 := by
    rw [sum_ite_mem, univ_inter]
    rfl
  rw [h2]
  calc ∑ x, iidPMF P n x * (if x ∈ robustTypicalSet P n ε then (0 : ℝ) else 1)
      = ∑ x, (iidPMF P n x - if x ∈ robustTypicalSet P n ε then iidPMF P n x else 0) :=
        sum_congr rfl fun x _ => by split_ifs <;> simp
    _ = _ := by rw [sum_sub_distrib, hμn.sum_eq_one]

/-- The covering of a layer is not missed, for `L ≥ e^{n b}` and `a < b`. -/
lemma tendsto_exp_neg_layer {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    Tendsto (fun n : ℕ => exp (-(exp (n * b) * (c * exp (-(n * a)))))) atTop (𝓝 0) := by
  refine tendsto_exp_neg_atTop_nhds_zero.comp ?_
  have e : ∀ n : ℕ, exp (n * b) * (c * exp (-(n * a))) = c * exp (n * (b - a)) := fun n => by
    rw [mul_left_comm, ← exp_add]
    congr 2
    ring
  simp only [e]
  refine Tendsto.const_mul_atTop hc (tendsto_exp_atTop.comp ?_)
  exact tendsto_natCast_atTop_atTop.atTop_mul_const (sub_pos.2 hab)

open Classical in
/-- **One layer of the covering**, as on page 21-7. If `L n k ≥ e^{n r}` with
`r > I(X; X̂_k | X̂_{k+1}, …)`, the layers from `k + 1` on extend to the layers from `k` on. -/
lemma lineCov_step (hμ : IsPMF μ) (k : Fin N) {r : ℝ} (hL : ∀ n : ℕ, exp (n * r) ≤ L n k)
    (hr : I[Prod.fst : fun z : α × ∀ l, β l => z.2 k |
      fun z => tailOf (k + 1 : ℕ) z.2 ; μ] < r)
    (h : LineCov μ L (k + 1 : ℕ)) : LineCov μ L k := by
  intro ε hε η hη
  set X : (α × ∀ l, β l) → α := Prod.fst with hX
  set V : (α × ∀ l, β l) → ∀ l, β l := fun z => tailOf (k + 1 : ℕ) z.2 with hV
  set Y : (α × ∀ l, β l) → β k := fun z => z.2 k with hY
  set Ik := I[X : Y | V ; μ] with hIk
  set c := log (Fintype.card (β k)) with hc
  have hc0 : 0 ≤ c := log_natCast_nonneg _
  set g := r - Ik with hg
  have hg0 : 0 < g := sub_pos.2 hr
  set ε₁ := min (min ε (1 / 2)) (g / (4 * (c + 1))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (lt_min hε (by norm_num)) (by positivity)
  have hε₁ε : ε₁ ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have hε₁2 : ε₁ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hε₁g : ε₁ * (2 * c) ≤ g / 2 := by
    have h₁ : ε₁ ≤ g / (4 * (c + 1)) := min_le_right _ _
    calc ε₁ * (2 * c) ≤ g / (4 * (c + 1)) * (2 * c) :=
          mul_le_mul_of_nonneg_right h₁ (by positivity)
      _ ≤ g / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hb₀ := eventually_sum_last_codebook_le hμ V X Y (ε := ε₁) (half_lt_self hε₁0) hε₁0
    (by linarith)
  have hlim := tendsto_exp_neg_layer (a := Ik + g / 2) (b := r) (c := 1 / 2)
    (by simp only [hg]; linarith) (by norm_num)
  filter_upwards [h (ε₁ / 2) (half_pos hε₁0) (η / 2) (half_pos hη), hb₀,
    (tendsto_order.1 hlim).2 (η / 2) (half_pos hη)] with n ⟨e, C, he0, hC, hsum⟩ hlast hsmall
  set P := dist μ X with hP
  have hPp : IsPMF P := hμ.dist _
  have hwn := iidPMF_isPMF hPp n
  set word : (∀ l', Fin (L n l')) → Fin n → ∀ l, β l := fun t i => tailOf (k + 1 : ℕ) fun l =>
    C l t i with hword
  set G : (Fin n → α) → Prop := fun x => zipSeq (word (e x)) x ∈
    robustTypicalSet (dist μ (pair V X)) n (ε₁ / 2) with hG
  -- the bound for one good source sequence
  have hη₀ : (0 : ℝ) ≤ η / 2 := (half_pos hη).le
  have hLpos : 0 < L n k := Nat.pos_of_ne_zero (NeZero.ne _)
  have hne𝒟 : Nonempty (Fin (L n k) → Fin n → β k) := ⟨fun _ _ => Classical.arbitrary _⟩
  have hneJ : Nonempty (Fin (L n k)) := ⟨⟨0, hLpos⟩⟩
  obtain ⟨D, f, hD⟩ := exists_layer hwn e G
    (fun i => iidPMF (channelExt (condDist μ Y V) n (word i)) (L n k))
    (fun i D x j => zipSeq (zipSeq (word i) x) (D j) ∈
      robustTypicalSet (triLaw μ V X Y) n ε₁) hη₀ (fun x hx => by
      refine ⟨iidPMF_isPMF (channelExt_condDist_isPMF hμ Y V
        (dist_ne_zero_of_mem hμ hx)) _, ?_⟩
      have hl' := hlast _ x hx (L n k)
      refine le_trans (le_of_eq (sum_congr rfl fun D _ => ?_)) (hl'.trans (le_trans ?_ hsmall.le))
      · congr!
      refine exp_le_exp.2 (neg_le_neg ?_)
      have h₁ : (1 / 2 : ℝ) * exp (-(n * (Ik + g / 2))) ≤
          (1 - ε₁) * exp (-(n * (Ik + ε₁ * (2 * c)))) := by
        refine mul_le_mul (by linarith) (exp_le_exp.2 ?_) (exp_pos _).le (by linarith)
        have : (n : ℝ) * (ε₁ * (2 * c)) ≤ n * (g / 2) :=
          mul_le_mul_of_nonneg_left hε₁g (Nat.cast_nonneg n)
        nlinarith
      exact mul_le_mul (hL n) h₁ (by positivity) (by positivity))
  -- the new encoder and codewords
  set e' : (Fin n → α) → ∀ l, Fin (L n l) := fun x => Function.update (e x) k (f x) with he'
  let clr : (∀ l, Fin (L n l)) → ∀ l, Fin (L n l) := fun t l =>
    if (k : ℕ) + 1 ≤ (l : ℕ) then t l else 0
  set C' : ∀ l, (∀ l', Fin (L n l')) → Fin n → β l :=
    Function.update C k fun t => D (clr t) (t k) with hC'
  have hclr : ∀ x, clr (e' x) = e x := fun x => by
    funext l
    simp only [clr, he']
    by_cases hl : (k : ℕ) + 1 ≤ l
    · have hne : l ≠ k := fun h' => by
        subst h'
        omega
      simp [hl, hne]
    · simp only [hl, ite_false]
      exact (he0 x l (by omega)).symm
  have hC'k : ∀ x, C' k (e' x) = D (e x) (f x) := fun x => by
    simp only [hC', Function.update_self]
    rw [hclr]
    simp [he']
  have hC'l : ∀ x (l : Fin N), k < l → C' l (e' x) = C l (e x) := fun x l hl => by
    have hne : l ≠ k := hl.ne'
    simp only [hC', Function.update_of_ne hne]
    refine hC l _ _ fun i hi => ?_
    have : i ≠ k := (hl.trans_le hi).ne'
    simp [he', this]
  refine ⟨e', C', fun x l hl => ?_, fun l t t' ht => ?_, ?_⟩
  · have hne : l ≠ k := fun h' => by
      subst h'
      omega
    simp only [he', Function.update_of_ne hne]
    exact he0 x l (by omega)
  · by_cases hl : l = k
    · subst hl
      simp only [hC', Function.update_self]
      have hk : t l = t' l := ht l le_rfl
      have hcl : clr t = clr t' := by
        funext i
        simp only [clr]
        split_ifs with hi
        · exact ht i (Fin.le_iff_val_le_val.2 (by omega))
        · rfl
      rw [hk, hcl]
    · simp only [hC', Function.update_of_ne hl]
      exact hC l t t' ht
  · -- the typicality
    set f₀ : ((∀ l, β l) × α) × β k → (∀ l, β l) × α := fun w => (Function.update w.1.1 k w.2,
      w.1.2)
      with hf₀
    have hdist : dist μ (pair (fun z : α × ∀ l, β l => tailOf k z.2) Prod.fst) =
        dist (triLaw μ V X Y) f₀ := by
      rw [triLaw, ← dist_comp_eq]
      congr 1
      funext z
      simp only [Function.comp, pair, hf₀, hV, hY, hX]
      rw [update_tailOf]
    have hword' : ∀ x i, tailOf k (fun l => C' l (e' x) i) =
        Function.update (word (e x) i) k (D (e x) (f x) i) := fun x i => by
      have e₁ : word (e x) i = tailOf (k + 1 : ℕ) fun l => C' l (e' x) i := by
        simp only [hword]
        funext l
        by_cases hl : (k : ℕ) + 1 ≤ l
        · simp [tailOf, hl, hC'l x l (Fin.lt_def.2 (by omega))]
        · simp [tailOf, hl]
      have e₂ := update_tailOf k fun l => C' l (e' x) i
      rw [← e₂, e₁, hC'k]
    have hpt : ∀ x, (if zipSeq (fun i => tailOf k fun l => C' l (e' x) i) x ∈
        robustTypicalSet (dist μ (pair (fun z : α × ∀ l, β l => tailOf k z.2) Prod.fst)) n ε
        then (0 : ℝ) else 1) ≤
        if G x ∧ zipSeq (zipSeq (word (e x)) x) (D (e x) (f x)) ∈
          robustTypicalSet (triLaw μ V X Y) n ε₁ then 0 else 1 := fun x => by
      by_cases hgood : G x ∧ zipSeq (zipSeq (word (e x)) x) (D (e x) (f x)) ∈
          robustTypicalSet (triLaw μ V X Y) n ε₁
      · have h₁ := comp_mem_robustTypicalSet hgood.2 f₀
        rw [← hdist] at h₁
        have h₂ := robustTypicalSet_mono (hμ.dist _).nonneg hε₁ε h₁
        have e₃ : f₀ ∘ zipSeq (zipSeq (word (e x)) x) (D (e x) (f x)) =
            zipSeq (fun i => tailOf k fun l => C' l (e' x) i) x := by
          funext i
          simp only [Function.comp, zipSeq, hf₀, hword']
        rw [e₃] at h₂
        simp [hgood, h₂]
      · simp only [hgood, ite_false]
        split_ifs <;> norm_num
    have hG' : ∑ x, iidPMF P n x * (if G x then (0 : ℝ) else 1) ≤ η / 2 := hsum
    calc _ ≤ ∑ x, iidPMF P n x * (if G x ∧ zipSeq (zipSeq (word (e x)) x) (D (e x) (f x)) ∈
          robustTypicalSet (triLaw μ V X Y) n ε₁ then 0 else 1) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hwn.nonneg x)
      _ ≤ ∑ x, iidPMF P n x * (if G x then (0 : ℝ) else 1) + η / 2 := by
          convert hD
      _ ≤ η := by linarith

/-- **The layered covering**: the layers from `1` on, with the rates `r l`, conditional on the later
layers. -/
theorem lineCov_of_rates (hμ : IsPMF μ) {r : Fin N → ℝ} (hL : ∀ (n : ℕ) (l : Fin N), 1 ≤ (l : ℕ) →
      exp (n * r l) ≤ L n l)
    (hr : ∀ l : Fin N, 1 ≤ (l : ℕ) → I[Prod.fst : fun z : α × ∀ l, β l => z.2 l |
      fun z => tailOf (l + 1 : ℕ) z.2 ; μ] < r l) (hN : 1 ≤ N) : LineCov μ L 1 := by
  have key : ∀ d : ℕ, d + 1 ≤ N → LineCov μ L (N - d) := by
    intro d
    induction d with
    | zero => exact fun _ => by simpa using lineCov_top hμ
    | succ d ih =>
      intro hd
      have hk : N - (d + 1) < N := by omega
      have h₁ : 1 ≤ N - (d + 1) := by omega
      have e : N - (d + 1) + 1 = N - d := by omega
      refine lineCov_step hμ ⟨N - (d + 1), hk⟩ (hL · _ h₁) (hr _ h₁) ?_
      simp only [e]
      exact ih (by omega)
  have := key (N - 1) (by omega)
  have e : N - (N - 1) = 1 := by omega
  rwa [e] at this

end Cover

/-! ### The line network -/

section Line

variable {m : ℕ} {β : Fin (m + 1) → Type*} [∀ l, Fintype (β l)] [∀ l, Nonempty (β l)]

/-- The parent in the line network. -/
def linePar (m : ℕ) (k : Fin (m + 1)) : Fin (m + 1) :=
  ⟨k - 1, by omega⟩

/-- The edges of the line network: from `k` to `k + 1`. -/
def lineEdges (m : ℕ) : Finset (Fin (m + 1) × Fin (m + 1)) := treeEdges 0 (linePar m)

lemma isRootedTree_line (m : ℕ) : IsRootedTree (0 : Fin (m + 1)) (linePar m) where
  root := by
    ext
    simp [linePar]
  lt := fun k hk => by
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    rw [Fin.lt_def]
    simp only [linePar]
    omega

lemma linePar_iterate (t : ℕ) (l : Fin (m + 1)) : ((linePar m)^[t] l : ℕ) = l - t := by
  induction t generalizing l with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [linePar]
    omega

/-- In the line network the node `k ≠ 0` is before the nodes from `k` on. -/
lemma mem_treeDesc_line {k : Fin (m + 1)} (hk : k ≠ 0) (l : Fin (m + 1)) :
    l ∈ treeDesc (linePar m) k ↔ k ≤ l := by
  have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
  simp only [treeDesc, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht⟩
    have := congrArg Fin.val ht
    rw [linePar_iterate] at this
    rw [Fin.le_def]
    omega
  · intro h
    refine ⟨l - k, Fin.ext ?_⟩
    rw [linePar_iterate]
    rw [Fin.le_def] at h
    omega

/-- The information at the nodes from `k` on is the information in the tail. -/
lemma mutualInfo_swRest_line {α : Type*} [Fintype α] {μ : (α × ∀ l, β l) → ℝ} (hμ : IsPMF μ)
    {k : Fin (m + 1)} (hk : k ≠ 0) :
    I[Prod.fst : fun z : α × ∀ l, β l => swRest (treeDesc (linePar m) k)ᶜ z.2 ; μ] =
      I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; μ] := by
  classical
  set S := (treeDesc (linePar m) k)ᶜ with hS
  have hmem : ∀ l : Fin (m + 1), l ∉ S ↔ (k : ℕ) ≤ l := fun l => by
    simp only [hS, mem_compl, not_not, mem_treeDesc_line hk, Fin.le_def]
  let f : (∀ l : {l // l ∉ S}, β l) → ∀ l, β l := fun v l =>
    if h : (k : ℕ) ≤ l then v ⟨l, (hmem l).2 h⟩ else Classical.arbitrary _
  have hf : Function.Injective f := fun v w h => by
    funext ⟨l, hl⟩
    have := congrFun h l
    simp only [f, dite_eq_left ((hmem l).1 hl)] at this
    exact this
  rw [mutualInfo_eq_entropy_sub_condEntropy hμ, mutualInfo_eq_entropy_sub_condEntropy hμ]
  congr 1
  refine (condEntropy_congr_right hμ Prod.fst (X := fun z : α × ∀ l, β l => swRest S z.2) f hf
    fun z => ?_).symm
  funext l
  by_cases h : (k : ℕ) ≤ l
  · simp only [tailOf, f, dite_eq_left h, ite_eq_left h]
    rfl
  · simp only [tailOf, f, dite_eq_right h, ite_eq_right h]

variable {α : Type*} [Fintype α] {P : α → ℝ} {d : ∀ l, α → β l → ℝ}

/-- If two random variables are functions of each other, conditioning on them is the same. -/
lemma condEntropy_eq_of_comp {Ω a b c : Type*} [Fintype Ω] [Fintype a] [Fintype b] [Fintype c]
    {μ : Ω → ℝ} (hμ : IsPMF μ) (X : Ω → a) {A : Ω → b} {B : Ω → c} (f : b → c) (g : c → b)
    (hf : B = f ∘ A) (hg : A = g ∘ B) : H[X | A ; μ] = H[X | B ; μ] := by
  refine le_antisymm ?_ ?_
  · have := condEntropy_le_condEntropy_comp hμ X A f
    rwa [← hf] at this
  · have := condEntropy_le_condEntropy_comp hμ X B g
    rwa [← hg] at this

/-- The chain rule along the tails. -/
lemma mutualInfo_tailOf {μ' : (α × ∀ l, β l) → ℝ} (hμ : IsPMF μ') (k : Fin (m + 1)) :
    I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; μ'] =
      I[Prod.fst : fun z : α × ∀ l, β l => tailOf (k + 1 : ℕ) z.2 ; μ'] +
      I[Prod.fst : fun z : α × ∀ l, β l => z.2 k | fun z => tailOf (k + 1 : ℕ) z.2 ; μ'] := by
  classical
  rw [← chain_rule_mutualInfo₂ hμ, mutualInfo_eq_entropy_sub_condEntropy hμ,
    mutualInfo_eq_entropy_sub_condEntropy hμ]
  congr 1
  refine condEntropy_eq_of_comp hμ _ (fun w => (w k, tailOf (k + 1 : ℕ) w))
    (fun w => Function.update w.2 k w.1) ?_ ?_
  · funext z
    simp only [Function.comp, pair]
    refine Prod.ext ?_ ?_
    · simp [tailOf]
    · funext l
      simp only [tailOf]
      split_ifs with h₁ h₂
      · rfl
      · omega
      · rfl
  · funext z
    simp only [Function.comp, pair]
    exact (update_tailOf k z.2).symm

/-- The sum of the conditional informations of the layers from `k` on is at most the information of
the tail. -/
lemma sum_condInfo_le {μ' : (α × ∀ l, β l) → ℝ} (hμ : IsPMF μ') (k : ℕ) (hk : k ≤ m + 1) :
    ∑ i ∈ univ.filter (fun i : Fin (m + 1) => k ≤ (i : ℕ)),
      I[Prod.fst : fun z : α × ∀ l, β l => z.2 i | fun z => tailOf (i + 1 : ℕ) z.2 ; μ'] ≤
      I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; μ'] := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, k = m + 1 - d := ⟨m + 1 - k, by omega⟩
  induction d with
  | zero =>
    have : (univ.filter fun i : Fin (m + 1) => m + 1 - 0 ≤ (i : ℕ)) = ∅ := by
      ext i
      have := i.isLt
      simp
      omega
    rw [this, sum_empty]
    exact mutualInfo_nonneg hμ _ _
  | succ d ih =>
    by_cases hd : d + 1 ≤ m + 1
    · have hk' : m + 1 - (d + 1) < m + 1 := by omega
      set K : Fin (m + 1) := ⟨m + 1 - (d + 1), hk'⟩ with hK
      have e : (univ.filter fun i : Fin (m + 1) => m + 1 - (d + 1) ≤ (i : ℕ)) =
          insert K (univ.filter fun i : Fin (m + 1) => m + 1 - d ≤ (i : ℕ)) := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_insert, hK, Fin.ext_iff]
        have := i.isLt
        omega
      have hnot : K ∉ univ.filter fun i : Fin (m + 1) => m + 1 - d ≤ (i : ℕ) := by
        simp only [mem_filter, mem_univ, true_and, hK]
        omega
      rw [e, sum_insert hnot]
      have h₁ := ih (by omega)
      have h₂ := mutualInfo_tailOf hμ K
      have e₂ : (K : ℕ) + 1 = m + 1 - d := by
        simp only [hK]
        omega
      have e₃ : (K : ℕ) = m + 1 - (d + 1) := rfl
      rw [e₂, e₃] at h₂
      rw [e₂]
      linarith
    · have e : m + 1 - (d + 1) = m + 1 - d := by omega
      rw [e]
      exact ih (by omega)

/-- The expected distortion under a typical pair, for the tail from `1`. -/
lemma sum_distortion_le {μ' : (α × ∀ l, β l) → ℝ} (hd : ∀ l x y, 0 ≤ d l x y)
    {n : ℕ} {ε : ℝ} {l : Fin (m + 1)} (hl : 1 ≤ (l : ℕ)) {x : Fin n → α}
    {w : Fin n → ∀ l, β l}
    (h : zipSeq (fun i => tailOf 1 (w i)) x ∈
      robustTypicalSet (dist μ' (pair (fun z : α × ∀ l, β l => tailOf 1 z.2) Prod.fst)) n ε) :
    ∑ i, d l (x i) (w i l) ≤ n * ((1 + ε) * ∑ z, μ' z * d l z.1 (z.2 l)) := by
  have h₁ := sum_le_card_mul_of_mem_robustTypicalSet h
    (g := fun v : (∀ l, β l) × α => d l v.2 (v.1 l)) fun v => hd _ _ _
  have e₁ : ∑ i, d l (x i) (w i l) = ∑ i, (fun v : (∀ l, β l) × α => d l v.2 (v.1 l))
      (zipSeq (fun i => tailOf 1 (w i)) x i) := by
    refine sum_congr rfl fun i _ => ?_
    simp [zipSeq, tailOf, hl]
  have e₂ : expect (dist μ' (pair (fun z : α × ∀ l, β l => tailOf 1 z.2) Prod.fst))
      (fun v : (∀ l, β l) × α => d l v.2 (v.1 l)) = ∑ z, μ' z * d l z.1 (z.2 l) := by
    rw [expect]
    simp only [mul_comm (d l _ _)]
    rw [sum_dist_mul]
    refine sum_congr rfl fun z _ => ?_
    simp [pair, tailOf, hl]
  rw [e₁]
  rwa [e₂] at h₁

/-- **Page 21-7 of [elgamal2010]: achievability for the line network.** If the rate into each node
`k` exceeds `I(X; X̂_k, X̂_{k+1}, …)`, then the rates are achievable. -/
theorem isAchievableMDN_line (hP : IsPMF P) (hd : ∀ l x y, 0 ≤ d l x y) {κ : α → (∀ l, β l) → ℝ}
    (hκ : IsChannel κ) {R : Fin (m + 1) → Fin (m + 1) → ℝ} {D : Fin (m + 1) → ℝ}
    (hR : ∀ j k, 0 ≤ R j k) (hR0 : ∀ j k, (j, k) ∉ lineEdges m → R j k = 0)
    (hD : ∀ l, l ≠ 0 → ∑ z, jointOf P κ z * d l z.1 (z.2 l) ≤ D l)
    (hI : ∀ k : Fin (m + 1), k ≠ 0 →
      I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; jointOf P κ] <
      R (linePar m k) k * log 2) :
    IsAchievableMDN P d 0 (lineEdges m) R D := by
  classical
  have hμ := jointOf_isPMF hP hκ
  set μ := jointOf P κ with hμd
  have hl2 := log_pos one_lt_two
  obtain ⟨a₀⟩ : Nonempty α := Fintype.card_pos_iff.1 (card_pos_of_isPMF hP)
  have hneα : Nonempty α := ⟨a₀⟩
  have hN0 : (0 : ℝ) < ((m : ℝ) + 2) := by positivity
  -- the margin
  obtain ⟨δ, hδ, hδI⟩ : ∃ δ > 0, ∀ k : Fin (m + 1), k ≠ 0 →
      I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; μ] + ((m : ℝ) + 2) * δ <
        R (linePar m k) k * log 2 := by
    set Gp : Fin (m + 1) → ℝ := fun k => R (linePar m k) k * log 2 -
      I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; μ] with hGp
    set A := univ.filter fun k : Fin (m + 1) => k ≠ 0 with hA
    rcases A.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun k hk => ?_⟩
      have hm : k ∈ A := mem_filter.2 ⟨mem_univ _, hk⟩
      rw [he] at hm
      simp at hm
    · obtain ⟨k₀, hk₀, hmin⟩ := A.exists_min_image Gp hne
      have hk₀' : k₀ ≠ 0 := (mem_filter.1 hk₀).2
      have hg : 0 < Gp k₀ := sub_pos.2 (hI k₀ hk₀')
      refine ⟨Gp k₀ / (2 * ((m : ℝ) + 2)), by positivity, fun k hk => ?_⟩
      have h₁ := hmin k (mem_filter.2 ⟨mem_univ _, hk⟩)
      have h₂ : ((m : ℝ) + 2) * (Gp k₀ / (2 * ((m : ℝ) + 2))) = Gp k₀ / 2 := by
        field_simp
      rw [h₂]
      simp only [hGp] at h₁ hg ⊢
      linarith
  -- the rates of the layers
  set I₀ : Fin (m + 1) → ℝ := fun i => I[Prod.fst : fun z : α × ∀ l, β l => z.2 i |
    fun z => tailOf (i + 1 : ℕ) z.2 ; μ] with hI₀
  have hI₀0 : ∀ i, 0 ≤ I₀ i := fun i => condMutualInfo_nonneg hμ _ _ _
  set r : Fin (m + 1) → ℝ := fun i => I₀ i + δ with hr
  have hr0 : ∀ i, 0 < r i := fun i => by
    have := hI₀0 i
    simp only [hr]
    linarith
  set L : ℕ → Fin (m + 1) → ℕ := fun n i => ⌈exp (n * r i)⌉₊ with hLd
  have hLne : ∀ n i, NeZero (L n i) := fun n i => ⟨(Nat.ceil_pos.2 (exp_pos _)).ne'⟩
  have hLle : ∀ (n : ℕ) i, exp (n * r i) ≤ L n i := fun n i => Nat.le_ceil _
  have hcov : LineCov μ L 1 := lineCov_of_rates hμ (r := r) (fun n l _ => hLle n l)
    (fun l _ => by
      have := hδ
      simp only [hr, hI₀]
      linarith) (by omega)
  have hPeq : dist μ Prod.fst = P := dist_jointOf_fst hκ
  refine ⟨hR, hR0, fun ε hε => ?_⟩
  -- the parameters
  set Bd := ∑ l, (∑ z, μ z * d l z.1 (z.2 l) + maxDistortion (d l)) + 1 with hBd
  have hE0 : ∀ l, 0 ≤ ∑ z, μ z * d l z.1 (z.2 l) := fun l =>
    sum_nonneg fun z _ => mul_nonneg (hμ.nonneg z) (hd _ _ _)
  have hdm0 : ∀ l, 0 ≤ maxDistortion (d l) := fun l => maxDistortion_nonneg (hd l)
  have hterm : ∀ l, ∑ z, μ z * d l z.1 (z.2 l) + maxDistortion (d l) ≤ Bd - 1 := fun l => by
    have := single_le_sum (f := fun l => ∑ z, μ z * d l z.1 (z.2 l) + maxDistortion (d l))
      (fun l _ => add_nonneg (hE0 l) (hdm0 l)) (mem_univ l)
    simp only [hBd]
    linarith
  have hBd0 : 0 < Bd := by
    have : 0 ≤ ∑ l, (∑ z, μ z * d l z.1 (z.2 l) + maxDistortion (d l)) :=
      sum_nonneg fun l _ => add_nonneg (hE0 l) (hdm0 l)
    simp only [hBd]
    linarith
  set ε₀ := ε / (2 * Bd) with hε₀
  have hε₀0 : 0 < ε₀ := by positivity
  have hsize : ∀ᶠ n : ℕ in atTop, ((m : ℝ) + 2) * log 2 ≤ n * δ := by
    have := tendsto_natCast_atTop_atTop.atTop_mul_const (r := δ) hδ
    exact this.eventually_ge_atTop _
  filter_upwards [hcov ε₀ hε₀0 ε₀ hε₀0, hsize, eventually_gt_atTop 0] with n hn hnsize hn0
  obtain ⟨e, C, he0, hC, hsum⟩ := hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [hPeq] at hsum
  -- the code
  set M : Fin (m + 1) → Fin (m + 1) → ℕ := fun j k => 2 ^ ⌊(n : ℝ) * R j k⌋₊ with hM
  have hMpos : ∀ j k, 0 < M j k := fun j k => by positivity
  let T := ∀ l, Fin (L n l)
  let part : Fin (m + 1) → Fin (m + 1) → T → T := fun j k t =>
    if (k : ℕ) = j + 1 then tailIdx (L n) k t else 0
  let merge : ∀ k, (∀ j, j < k → T) → T := fun k w =>
    if hk : k ≠ 0 then w (linePar m k) ((isRootedTree_line m).lt k hk) else 0
  have hpar : ∀ k : Fin (m + 1), k ≠ 0 → (k : ℕ) = (linePar m k : ℕ) + 1 := fun k hk => by
    have : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp only [linePar]
    omega
  have hcard : ∀ j k, Nat.card (Set.range (part j k)) ≤ M j k := fun j k => by
    by_cases hjk : (k : ℕ) = j + 1
    · -- the number of tails
      have hjne : k ≠ 0 := fun h => by
        rw [h] at hjk
        simp at hjk
      have hjp : linePar m k = j := Fin.ext (by
        simp only [linePar]
        omega)
      set Q := {i : Fin (m + 1) // (k : ℕ) ≤ i} with hQ
      have h₁ : Nat.card (Set.range (part j k)) ≤ Nat.card (∀ i : Q, Fin (L n i)) := by
        refine Nat.card_le_card_of_injective (fun t i => t.val i) ?_
        rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ h
        have h₂ := fun i => congrFun h i
        simp only [part, hjk, ite_true] at h₂ ⊢
        refine Subtype.ext ?_
        funext i
        simp only [tailIdx]
        by_cases hi : (k : ℕ) ≤ i
        · have hi' : (j : ℕ) + 1 ≤ i := hjk ▸ hi
          have := h₂ ⟨i, hi⟩
          simp only [tailIdx, hi', ite_true] at this
          rw [ite_eq_left hi', ite_eq_left hi']
          exact this
        · have hi' : ¬ (j : ℕ) + 1 ≤ i := hjk ▸ hi
          rw [ite_eq_right hi', ite_eq_right hi']
      refine h₁.trans ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_pi]
      simp only [Fintype.card_fin]
      -- the size
      have hpr : ((∏ i : Q, L n i : ℕ) : ℝ) ≤ exp ((n : ℝ) * (R j k * log 2) - log 2) := by
        have hpt : ∀ i : Q, (L n i : ℝ) ≤ exp (log 2 + n * r i) := fun i => by
          have h₂ : (L n i : ℝ) < exp (n * r i) + 1 := Nat.ceil_lt_add_one (exp_pos _).le
          have h₃ : 1 ≤ exp ((n : ℝ) * r i) := one_le_exp (by
            have := hr0 i
            positivity)
          rw [exp_add, exp_log (by norm_num)]
          linarith
        push_cast
        refine (prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) fun i _ => hpt i).trans ?_
        rw [← exp_sum]
        refine exp_le_exp.2 ?_
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_univ, ← mul_sum]
        have hQcard : (Fintype.card Q : ℝ) ≤ (m : ℝ) + 1 := by
          have : Fintype.card Q ≤ Fintype.card (Fin (m + 1)) := Fintype.card_subtype_le _
          rw [Fintype.card_fin] at this
          exact_mod_cast this
        have hsumr : ∑ i : Q, r i ≤ I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; μ] +
            ((m : ℝ) + 1) * δ := by
          have e₁ : ∑ i : Q, r i = ∑ i ∈ univ.filter (fun i : Fin (m + 1) => (k : ℕ) ≤ (i : ℕ)),
              r i := (sum_subtype _ (by simp) r).symm
          rw [e₁, sum_add_distrib]
          have h₄ := sum_condInfo_le hμ (k : ℕ) k.isLt.le
          have h₅ : ∑ _i ∈ univ.filter (fun i : Fin (m + 1) => (k : ℕ) ≤ (i : ℕ)), δ ≤
              ((m : ℝ) + 1) * δ := by
            rw [sum_const, nsmul_eq_mul]
            refine mul_le_mul_of_nonneg_right ?_ hδ.le
            have := card_le_univ (univ.filter fun i : Fin (m + 1) => (k : ℕ) ≤ (i : ℕ))
            rw [Fintype.card_fin] at this
            exact_mod_cast this
          simp only [hI₀] at *
          linarith
        have hgap := hδI k hjne
        rw [hjp] at hgap
        have h₆ : (Fintype.card Q : ℝ) * log 2 ≤ ((m : ℝ) + 1) * log 2 :=
          mul_le_mul_of_nonneg_right hQcard hl2.le
        have h₇ : (n : ℝ) * ∑ i : Q, r i ≤ n * (I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ;
            μ] + ((m : ℝ) + 1) * δ) := mul_le_mul_of_nonneg_left hsumr hn'.le
        have h₈ : (n : ℝ) * (I[Prod.fst : fun z : α × ∀ l, β l => tailOf k z.2 ; μ] +
            ((m : ℝ) + 2) * δ) ≤ n * (R j k * log 2) :=
          mul_le_mul_of_nonneg_left hgap.le hn'.le
        nlinarith
      have h₉ := hpr.trans (exp_le_two_pow_floor n (R j k))
      exact_mod_cast h₉
    · -- a pair that is not an edge
      have h₁ : Nat.card (Set.range (part j k)) ≤ Nat.card Unit :=
        Nat.card_le_card_of_injective (fun _ => ()) (by
          rintro ⟨_, t, rfl⟩ ⟨_, t', rfl⟩ _
          refine Subtype.ext ?_
          simp only [part, ite_eq_right hjk])
      simp only [Nat.card_unique] at h₁
      exact h₁.trans (hMpos j k)
  have hne : Nonempty T := ⟨0⟩
  obtain ⟨c, hc⟩ := MDNetCode.ofParts (s := (0 : Fin (m + 1))) (M := M) (T := T) (n := n)
    (α := α) (β := β) part (fun k t => tailIdx (L n) k t) merge e C hcard
    (fun k t hk => by
      simp only [merge, hk, ne_eq, not_false_eq_true, ↓reduceDIte, part]
      rw [ite_eq_left (hpar k hk)])
    (fun k l t hk => by
      simp only [part]
      split_ifs with h
      · funext i
        simp only [tailIdx, h]
        by_cases hi : (k : ℕ) + 1 ≤ i
        · have : (k : ℕ) ≤ i := by omega
          simp [hi, this]
        · simp [hi]
      · rfl)
    (fun l t hl => by
      refine hC l _ _ fun i hi => ?_
      have : (l : ℕ) ≤ i := Fin.le_def.1 hi
      simp [tailIdx, this])
  refine ⟨c, fun l hl => ?_⟩
  have hl1 : 1 ≤ (l : ℕ) := by
    have : (l : ℕ) ≠ 0 := fun h => hl (Fin.ext h)
    omega
  have hdl := hD l hl
  -- the distortion for one source sequence
  set p := iidPMF P n with hp
  have hpp : IsPMF p := iidPMF_isPMF hP n
  have hpt : ∀ x, seqDistortion (d l) x (C l (e x)) ≤
      (1 + ε₀) * (∑ z, μ z * d l z.1 (z.2 l)) + maxDistortion (d l) *
        (if zipSeq (fun i => tailOf 1 fun l => C l (e x) i) x ∈
        robustTypicalSet (dist μ (pair (fun z : α × ∀ l, β l => tailOf 1 z.2) Prod.fst)) n ε₀
        then 0 else 1) := fun x => by
    have hE := hE0 l
    have hne₁ : Nonempty α := ⟨a₀⟩
    by_cases ht : zipSeq (fun i => tailOf 1 fun l => C l (e x) i) x ∈
        robustTypicalSet (dist μ (pair (fun z : α × ∀ l, β l => tailOf 1 z.2) Prod.fst)) n ε₀
    · simp only [ht, ite_true, mul_zero, add_zero]
      have h₁ := sum_distortion_le hd hl1 ht
      rw [seqDistortion, div_le_iff₀ hn']
      linarith
    · simp only [ht, ite_false, mul_one]
      have h₁ := seqDistortion_le_maxDistortion (d l) hn0 x (C l (e x))
      have h₂ : 0 ≤ (1 + ε₀) * ∑ z, μ z * d l z.1 (z.2 l) := by positivity
      linarith
  have hfinal : c.distortion P d l ≤ (1 + ε₀) * (∑ z, μ z * d l z.1 (z.2 l)) +
      maxDistortion (d l) * ε₀ := by
    simp only [MDNetCode.distortion, hc _ l hl]
    calc ∑ x, iidPMF P n x * seqDistortion (d l) x (C l (e x))
        ≤ ∑ x, p x * ((1 + ε₀) * (∑ z, μ z * d l z.1 (z.2 l)) + maxDistortion (d l) *
          (if zipSeq (fun i => tailOf 1 fun l => C l (e x) i) x ∈
          robustTypicalSet (dist μ (pair (fun z : α × ∀ l, β l => tailOf 1 z.2) Prod.fst)) n ε₀
          then 0 else 1)) := sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hpp.nonneg x)
      _ = (1 + ε₀) * (∑ z, μ z * d l z.1 (z.2 l)) + maxDistortion (d l) * ∑ x, p x *
          (if zipSeq (fun i => tailOf 1 fun l => C l (e x) i) x ∈
          robustTypicalSet (dist μ (pair (fun z : α × ∀ l, β l => tailOf 1 z.2) Prod.fst)) n ε₀
          then 0 else 1) := by
          simp only [mul_add, sum_add_distrib]
          congr 1
          · rw [← sum_mul, hpp.sum_eq_one, one_mul]
          · rw [mul_sum]
            exact sum_congr rfl fun x _ => by ring
      _ ≤ _ := by
          refine add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (hdm0 l))
  have hb₁ := hterm l
  have hE := hE0 l
  have hm := hdm0 l
  have hscale : ε₀ * (Bd - 1) ≤ ε / 2 := by
    have : ε₀ * Bd = ε / 2 := by
      rw [hε₀]
      field_simp
    nlinarith
  have : ε₀ * (∑ z, μ z * d l z.1 (z.2 l) + maxDistortion (d l)) ≤ ε₀ * (Bd - 1) :=
    mul_le_mul_of_nonneg_left hb₁ hε₀0.le
  nlinarith

/-- **Theorem 1 of Lecture 21 of [elgamal2010], page 21-6, for the line network.** The
rate–distortion region is the set of the rate tuples on the edges with `R_{k-1,k} ≥ I(X; X̂(S_kᶜ))`
for some `p(x̂ | x)` with the prescribed distortions. -/
theorem mdnRegion_line_eq (hP : IsPMF P) (hd : ∀ l x y, 0 ≤ d l x y) (D : Fin (m + 1) → ℝ) :
    mdnRegion P d 0 (lineEdges m) D = {R | (∀ j k, 0 ≤ R j k) ∧
      (∀ j k, (j, k) ∉ lineEdges m → R j k = 0) ∧ ∃ κ : α → (∀ l, β l) → ℝ, IsChannel κ ∧
      (∀ l, l ≠ 0 → ∑ z, jointOf P κ z * d l z.1 (z.2 l) ≤ D l) ∧
      ∀ k, k ≠ 0 →
        I[Prod.fst : fun z : α × ∀ l, β l => swRest (treeDesc (linePar m) k)ᶜ z.2 ; jointOf P κ] ≤
          R (linePar m k) k * log 2} := by
  classical
  ext R
  constructor
  · intro h
    have hcl : IsClosed {R : Fin (m + 1) → Fin (m + 1) → ℝ | (∀ j k, 0 ≤ R j k) ∧
        ∀ j k, (j, k) ∉ lineEdges m → R j k = 0} := by
      have e : {R : Fin (m + 1) → Fin (m + 1) → ℝ | (∀ j k, 0 ≤ R j k) ∧
          ∀ j k, (j, k) ∉ lineEdges m → R j k = 0} =
          (⋂ j, ⋂ k, {R | 0 ≤ R j k}) ∩ ⋂ j, ⋂ k, ⋂ _ : (j, k) ∉ lineEdges m, {R | R j k = 0} := by
        ext R
        simp only [Set.mem_inter_iff, Set.mem_iInter]
        rfl
      rw [e]
      refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun k =>
        isClosed_le continuous_const (by fun_prop)) (isClosed_iInter fun j => isClosed_iInter
        fun k => isClosed_iInter fun _ => isClosed_eq (by fun_prop) continuous_const)
    have hsub : {R | IsAchievableMDN P d 0 (lineEdges m) R D} ⊆
        {R : Fin (m + 1) → Fin (m + 1) → ℝ | (∀ j k, 0 ≤ R j k) ∧
          ∀ j k, (j, k) ∉ lineEdges m → R j k = 0} := fun R' hR' => ⟨hR'.1, hR'.2.1⟩
    have hmem := closure_minimal hsub hcl h
    exact ⟨hmem.1, hmem.2, mdnCutset_tree hP (isRootedTree_line m) h hmem.2⟩
  · rintro ⟨hR, hR0, κ, hκ, hD, hI⟩
    have hμ := jointOf_isPMF hP hκ
    set Rn : ℕ → Fin (m + 1) → Fin (m + 1) → ℝ := fun t j k =>
      R j k + (if (j, k) ∈ lineEdges m then 1 / ((t : ℝ) + 1) else 0) with hRn
    have hlim : Tendsto Rn atTop (𝓝 R) := by
      refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun k => ?_
      by_cases hjk : (j, k) ∈ lineEdges m
      · simp only [hRn, hjk, ite_true]
        simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      · simp [hRn, hjk]
    refine mem_closure_of_tendsto hlim (Eventually.of_forall fun t => ?_)
    have hp : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
    refine isAchievableMDN_line hP hd hκ (fun j k => ?_) (fun j k hjk => ?_) hD fun k hk => ?_
    · simp only [hRn]
      have := hR j k
      split_ifs <;> linarith
    · simp only [hRn, hjk, ite_false, add_zero]
      exact hR0 j k hjk
    · have hedge : (linePar m k, k) ∈ lineEdges m :=
        mem_image.2 ⟨k, mem_filter.2 ⟨mem_univ _, hk⟩, rfl⟩
      simp only [hRn, hedge, ite_true]
      rw [← mutualInfo_swRest_line hμ hk]
      have := hI k hk
      have hl2 := log_pos one_lt_two
      nlinarith [mul_pos hp hl2]

end Line

end InfoTheory
