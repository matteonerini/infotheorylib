/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.SourceCoding.Code

/-!
# The Kraft and McMillan inequalities

The codeword lengths `l(x)` of a `D`-ary prefix code satisfy the Kraft inequality
`∑ₓ D^{-l(x)} ≤ 1`, and conversely any lengths satisfying it are the lengths of a prefix code. By
McMillan's theorem the same holds for uniquely decodable codes. The necessity directions for
finite codes are in Mathlib
(`InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one` and
`InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one`).

## Main definitions

* `wordVal D w`: the number with base-`D` digits `w` (most significant first).
* `natToWord D l N`: the `l`-digit base-`D` expansion of `N`.

## Main statements

* `kraft_of_isPrefixCode`, `exists_prefixCode_of_kraft`: Theorem 5.2.1.
* `summable_kraft_of_isPrefixCode`, `exists_prefixCode_of_summable`: Theorem 5.2.2, the extended
  Kraft inequality for countably infinite codes.
* `kraft_of_isUniquelyDecodableCode`, `exists_uniquelyDecodableCode_of_kraft`: Theorem 5.5.1
  (McMillan).
* `summable_kraft_of_isUniquelyDecodableCode`: McMillan's inequality for infinite alphabets.
* `exists_prefixCode_iff_exists_uniquelyDecodableCode`: uniquely decodable codes allow no other
  codeword lengths than prefix codes.

## Implementation notes

The converse is proved by assigning to the codewords, in order of increasing length, consecutive
intervals of the unit interval, as in the proof of Theorem 5.2.2. This handles finite and
countably infinite codes at once.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Sections 5.2 and
  5.5
-/

open Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### Words as numbers -/

section Words

variable {D : ℕ}

/-- The number `y₁ D^{l-1} + ⋯ + y_l` with base-`D` digits `w = y₁ ⋯ y_l`. -/
def wordVal (D : ℕ) (w : List (Fin D)) : ℕ :=
  w.foldl (fun (a : ℕ) (d : Fin D) => a * D + (d : ℕ)) 0

lemma foldl_wordVal (w : List (Fin D)) (a : ℕ) :
    w.foldl (fun (a : ℕ) (d : Fin D) => a * D + (d : ℕ)) a = a * D ^ w.length + wordVal D w := by
  induction w generalizing a with
  | nil => simp [wordVal]
  | cons d w ih =>
    simp only [List.foldl_cons, List.length_cons, wordVal]
    rw [ih, ih (0 * D + (d : ℕ))]
    ring

lemma wordVal_append (u v : List (Fin D)) :
    wordVal D (u ++ v) = wordVal D u * D ^ v.length + wordVal D v := by
  rw [wordVal, List.foldl_append, foldl_wordVal]
  rfl

lemma wordVal_lt (w : List (Fin D)) : wordVal D w < D ^ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [wordVal]
  | append_singleton u d ih =>
    have h1 : wordVal D [d] = d := by simp [wordVal]
    rw [wordVal_append, h1, List.length_singleton, pow_one, List.length_append,
      List.length_singleton, pow_succ]
    have := d.isLt
    nlinarith

/-- The `l`-digit base-`D` expansion of `N` (of `N mod Dˡ`), most significant digit first. -/
def natToWord (D : ℕ) [NeZero D] : ℕ → ℕ → List (Fin D)
  | 0, _ => []
  | l + 1, N => natToWord D l (N / D) ++ [Fin.ofNat D N]

variable [NeZero D]

@[simp] lemma length_natToWord (l N : ℕ) : (natToWord D l N).length = l := by
  induction l generalizing N with
  | zero => rfl
  | succ l ih => simp [natToWord, ih]

lemma wordVal_natToWord (l N : ℕ) : wordVal D (natToWord D l N) = N % D ^ l := by
  induction l generalizing N with
  | zero => simp [natToWord, wordVal, Nat.mod_one]
  | succ l ih =>
    rw [natToWord, wordVal_append, ih, List.length_singleton, pow_one, pow_succ]
    have h1 : wordVal D [Fin.ofNat D N] = N % D := by simp [wordVal]
    rw [h1, mul_comm (D ^ l) D, Nat.mod_mul]
    ring

lemma natToWord_wordVal (w : List (Fin D)) : natToWord D w.length (wordVal D w) = w := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton u d ih =>
    have h1 : wordVal D [d] = d := by simp [wordVal]
    rw [List.length_append, List.length_singleton, natToWord, wordVal_append, h1,
      List.length_singleton, pow_one]
    have hd := d.isLt
    have e1 : (wordVal D u * D + d) / D = wordVal D u := by
      rw [mul_comm, Nat.mul_add_div hD, Nat.div_eq_of_lt hd, add_zero]
    have e2 : (Fin.ofNat D (wordVal D u * D + d) : Fin D) = d := by
      ext; simp [Nat.mod_eq_of_lt hd]
    rw [e1, e2, ih]

omit [NeZero D] in
/-- If `u` is a prefix of `v`, then the first `|u|` digits of `v` are `u`:
`⌊val(v) / D^{|v|-|u|}⌋ = val(u)`. -/
lemma wordVal_div_of_prefix (hD : 0 < D) {u v : List (Fin D)} (h : u <+: v) :
    wordVal D v / D ^ (v.length - u.length) = wordVal D u := by
  obtain ⟨t, rfl⟩ := h
  rw [wordVal_append, List.length_append, Nat.add_sub_cancel_left, mul_comm,
    Nat.mul_add_div (pow_pos hD _), Nat.div_eq_of_lt (wordVal_lt t), add_zero]

end Words

/-! ### Prefixes and injective maps -/

lemma prefix_of_map_prefix {β γ : Type*} {f : β → γ} (hf : Function.Injective f)
    {u v : List β} (h : u.map f <+: v.map f) : u <+: v := by
  rw [List.prefix_iff_eq_take, List.length_map, ← List.map_take] at h
  rw [List.prefix_iff_eq_take]
  exact List.map_injective_iff.2 hf h

/-! ### The construction of a prefix code -/

/-- Assign codewords in an order `bef` compatible with the lengths: the codeword of `i` is the
first `lᵢ` digits of `∑_{j before i} D^{-lⱼ}`. If every `i` satisfies the Kraft inequality
together with its predecessors, the codewords form a prefix code. -/
theorem exists_prefix_words {ι : Type*} {D : ℕ} [NeZero D] (l : ι → ℕ) (bef : ι → ι → Prop)
    (htrans : ∀ i j k, bef i j → bef j k → bef i k) (hirr : ∀ i, ¬ bef i i)
    (htot : ∀ i j, i ≠ j → bef i j ∨ bef j i) (hmono : ∀ i j, bef j i → l j ≤ l i)
    (pred : ι → Finset ι) (hpred : ∀ i j, j ∈ pred i ↔ bef j i)
    (hkraft : ∀ i, ∑ j ∈ pred i, (1 / D : ℝ) ^ l j + (1 / D : ℝ) ^ l i ≤ 1) :
    ∃ c : ι → List (Fin D), (∀ i, (c i).length = l i) ∧ ∀ i j, c i <+: c j → i = j := by
  classical
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set N : ι → ℕ := fun i => ∑ j ∈ pred i, D ^ (l i - l j)
  -- `Nᵢ + 1 ≤ D^{lᵢ}`, from the Kraft inequality.
  have key1 : ∀ i, N i < D ^ l i := by
    intro i
    have hcast : ((N i : ℕ) : ℝ) = ∑ j ∈ pred i, (D : ℝ) ^ l i * (1 / D) ^ l j := by
      simp only [N, Nat.cast_sum, Nat.cast_pow]
      refine sum_congr rfl fun j hj => ?_
      rw [pow_sub₀ _ hDr.ne' (hmono i j ((hpred i j).1 hj)), one_div_pow, one_div]
    have h1 : ((N i : ℕ) : ℝ) + 1 ≤ (D : ℝ) ^ l i := by
      rw [hcast, ← mul_sum]
      have := mul_le_mul_of_nonneg_left (hkraft i) (pow_nonneg hDr.le (l i))
      rw [mul_add, one_div_pow, mul_one_div_cancel (pow_ne_zero _ hDr.ne'), mul_one] at this
      exact this
    have : ((N i + 1 : ℕ) : ℝ) ≤ ((D ^ l i : ℕ) : ℝ) := by push_cast; exact h1
    exact_mod_cast this
  -- `Nᵢ ≥ D^{lᵢ - lⱼ} (Nⱼ + 1)` when `j` comes before `i`.
  have key2 : ∀ i j, bef j i → D ^ (l i - l j) * (N j + 1) ≤ N i := by
    intro i j hji
    have hsub : insert j (pred j) ⊆ pred i := by
      intro k hk
      rw [mem_insert] at hk
      rcases hk with rfl | hk
      · exact (hpred i k).2 hji
      · exact (hpred i k).2 (htrans k j i ((hpred j k).1 hk) hji)
    have hj : j ∉ pred j := fun h => hirr j ((hpred j j).1 h)
    calc D ^ (l i - l j) * (N j + 1)
        = ∑ k ∈ insert j (pred j), D ^ (l i - l k) := by
          rw [sum_insert hj, mul_add, mul_one, add_comm, mul_sum]
          congr 1
          refine sum_congr rfl fun k hk => ?_
          rw [← pow_add]
          congr 1
          have h1 := hmono j k ((hpred j k).1 hk)
          have h2 := hmono i j hji
          omega
      _ ≤ N i := sum_le_sum_of_subset hsub
  refine ⟨fun i => natToWord D (l i) (N i), fun i => length_natToWord _ _, fun i j h => ?_⟩
  by_contra hij
  have hlen : l i ≤ l j := by simpa using h.length_le
  have hv := wordVal_div_of_prefix hD h
  simp only [length_natToWord, wordVal_natToWord, Nat.mod_eq_of_lt (key1 _)] at hv
  rcases htot i j hij with hb | hb
  · have := key2 j i hb
    have : N i + 1 ≤ N j / D ^ (l j - l i) :=
      (Nat.le_div_iff_mul_le (pow_pos hD _)).2 (by linarith)
    omega
  · have hl : l i = l j := le_antisymm hlen (hmono i j hb)
    have := key2 i j hb
    rw [hl, Nat.sub_self, pow_zero, one_mul] at this
    rw [hl, Nat.sub_self, pow_zero, Nat.div_one] at hv
    omega

/-! ### Kraft's inequality -/

variable {X α : Type*}

/-- **Theorem 5.2.1 (Kraft inequality), (5.6).** The codeword lengths of a `D`-ary prefix code
satisfy `∑ₓ D^{-l(x)} ≤ 1`. -/
theorem kraft_of_isPrefixCode [Fintype X] [Fintype α] [Nonempty α] {C : X → List α}
    (hC : IsPrefixCode C) : ∑ x, (1 / Fintype.card α : ℝ) ^ (C x).length ≤ 1 := by
  classical
  have h := InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one
    (S := univ.image C) (by
      rw [coe_image, coe_univ, Set.image_univ]
      exact (isPrefixCode_iff.1 hC).2)
  rwa [sum_image fun x _ y _ hxy => hC.injective hxy] at h

/-- **Theorem 5.2.2 (extended Kraft inequality), (5.9).** The codeword lengths of a prefix code
with countably (or arbitrarily) many codewords satisfy `∑ D^{-lᵢ} ≤ 1`. -/
theorem summable_kraft_of_isPrefixCode [Fintype α] [Nonempty α] {C : X → List α}
    (hC : IsPrefixCode C) :
    Summable (fun x => (1 / Fintype.card α : ℝ) ^ (C x).length) ∧
      ∑' x, (1 / Fintype.card α : ℝ) ^ (C x).length ≤ 1 := by
  have hpf := (isPrefixCode_iff.1 hC).2
  set e := Equiv.ofInjective C hC.injective
  have hs := InformationTheory.IsPrefixFree.summable_one_div_card_pow_length hpf
  have ht := InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one hpf
  refine ⟨?_, ?_⟩
  · have := (e.summable_iff (f := fun w : Set.range C =>
      (1 / (Fintype.card α : ℝ)) ^ (w : List α).length)).2 hs
    exact this
  · rw [← e.tsum_eq] at ht
    exact ht

/-- A family of lengths satisfying the (extended) Kraft inequality is the family of lengths of a
prefix code, for any countable (`Encodable`) set of symbols. -/
theorem exists_prefixCode_of_summable [Encodable X] [Fintype α] [Nonempty α] (l : X → ℕ)
    (hs : Summable fun x => (1 / Fintype.card α : ℝ) ^ l x)
    (h : ∑' x, (1 / Fintype.card α : ℝ) ^ l x ≤ 1) :
    ∃ C : X → List α, IsPrefixCode C ∧ ∀ x, (C x).length = l x := by
  classical
  set D := Fintype.card α
  have hD : 0 < D := Fintype.card_pos
  have : NeZero D := ⟨hD.ne'⟩
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  set f : X → ℝ := fun x => (1 / D : ℝ) ^ l x
  have hf0 : ∀ x, 0 ≤ f x := fun x => pow_nonneg (by positivity) _
  -- Order the symbols by length, breaking ties with an encoding.
  let bef : X → X → Prop := fun j i =>
    l j < l i ∨ (l j = l i ∧ Encodable.encode j < Encodable.encode i)
  -- Only finitely many symbols have length at most `L`.
  have hfin : ∀ i, {j | l j ≤ l i}.Finite := by
    intro i
    have hε : 0 < f i := pow_pos (by positivity) _
    have := (hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hε))
    rw [Filter.eventually_cofinite] at this
    refine this.subset fun j hj => ?_
    simp only [Set.mem_ofPred_eq, not_lt]
    exact pow_le_pow_of_le_one (by positivity) (div_le_one_of_le₀ (by exact_mod_cast hD)
      hDr.le) hj
  let pred : X → Finset X := fun i => ((hfin i).toFinset).filter fun j => bef j i
  have hpred : ∀ i j, j ∈ pred i ↔ bef j i := by
    intro i j
    simp only [pred, mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, and_iff_right_iff_imp]
    rintro (h | h)
    · exact h.le
    · exact h.1.le
  have hkraft : ∀ i, ∑ j ∈ pred i, f j + f i ≤ 1 := by
    intro i
    have hi : i ∉ pred i := fun hh => by
      rcases (hpred i i).1 hh with h | h
      · exact lt_irrefl _ h
      · exact lt_irrefl _ h.2
    rw [add_comm, ← sum_insert hi]
    exact (hs.sum_le_tsum _ fun j _ => hf0 j).trans h
  obtain ⟨c, hlen, hpf⟩ := exists_prefix_words (D := D) l bef
    (fun i j k hij hjk => by
      rcases hij with h1 | h1 <;> rcases hjk with h2 | h2
      · exact Or.inl (h1.trans h2)
      · exact Or.inl (h2.1 ▸ h1)
      · exact Or.inl (h1.1 ▸ h2)
      · exact Or.inr ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩)
    (fun i h => by rcases h with h | h <;> [exact lt_irrefl _ h; exact lt_irrefl _ h.2])
    (fun i j hij => by
      rcases lt_trichotomy (l i) (l j) with h | h | h
      · exact Or.inl (Or.inl h)
      · rcases lt_trichotomy (Encodable.encode i) (Encodable.encode j) with h' | h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact absurd (Encodable.encode_injective h') hij
        · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
      · exact Or.inr (Or.inl h))
    (fun i j h => by rcases h with h | h <;> [exact h.le; exact h.1.le])
    pred hpred hkraft
  set eα := Fintype.equivFin α
  refine ⟨fun x => (c x).map eα.symm, fun x y hxy => hpf x y ?_, fun x => by simp [hlen]⟩
  exact prefix_of_map_prefix eα.symm.injective hxy

/-- **Theorem 5.2.1 (Kraft inequality, converse).** Given lengths with `∑ₓ D^{-l(x)} ≤ 1`, there
is a `D`-ary prefix code with these codeword lengths. -/
theorem exists_prefixCode_of_kraft [Fintype X] [Fintype α] [Nonempty α] (l : X → ℕ)
    (h : ∑ x, (1 / Fintype.card α : ℝ) ^ l x ≤ 1) :
    ∃ C : X → List α, IsPrefixCode C ∧ ∀ x, (C x).length = l x := by
  let := Fintype.toEncodable X
  exact exists_prefixCode_of_summable l (Summable.of_finite) (by rwa [tsum_fintype])

/-! ### McMillan's inequality -/

/-- **Theorem 5.5.1 (McMillan), (5.48).** The codeword lengths of any uniquely decodable code
satisfy the Kraft inequality. -/
theorem kraft_of_isUniquelyDecodableCode [Fintype X] [Fintype α] [Nonempty α] {C : X → List α}
    (hC : IsUniquelyDecodableCode C) :
    ∑ x, (1 / Fintype.card α : ℝ) ^ (C x).length ≤ 1 := by
  classical
  obtain ⟨hinj, hud⟩ := isUniquelyDecodableCode_iff.1 hC
  have h := InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one
    (S := univ.image C) (by
      rw [coe_image, coe_univ, Set.image_univ]
      exact hud)
  rwa [sum_image fun x _ y _ hxy => hinj hxy] at h

/-- **Theorem 5.5.1 (McMillan, converse).** Given lengths satisfying the Kraft inequality, there is
a uniquely decodable code (indeed a prefix code) with these lengths. -/
theorem exists_uniquelyDecodableCode_of_kraft [Fintype X] [Nontrivial X] [Fintype α] [Nonempty α]
    (l : X → ℕ) (h : ∑ x, (1 / Fintype.card α : ℝ) ^ l x ≤ 1) :
    ∃ C : X → List α, IsUniquelyDecodableCode C ∧ ∀ x, (C x).length = l x := by
  obtain ⟨C, hC, hl⟩ := exists_prefixCode_of_kraft l h
  exact ⟨C, hC.isUniquelyDecodableCode', hl⟩

lemma isUniquelyDecodable_anti {S T : Set (List α)} (hST : S ⊆ T)
    (hT : InformationTheory.IsUniquelyDecodable T) : InformationTheory.IsUniquelyDecodable S :=
  fun L₁ L₂ h₁ h₂ h => hT L₁ L₂ (fun w hw => hST (h₁ w hw)) (fun w hw => hST (h₂ w hw)) h

/-- **Corollary (McMillan for infinite alphabets), (5.60).** A uniquely decodable code for an
infinite source alphabet also satisfies the Kraft inequality. -/
theorem summable_kraft_of_isUniquelyDecodableCode [Fintype α] [Nonempty α] {C : X → List α}
    (hC : IsUniquelyDecodableCode C) :
    Summable (fun x => (1 / Fintype.card α : ℝ) ^ (C x).length) ∧
      ∑' x, (1 / Fintype.card α : ℝ) ^ (C x).length ≤ 1 := by
  classical
  obtain ⟨hinj, hud⟩ := isUniquelyDecodableCode_iff.1 hC
  have hfin : ∀ F : Finset X, ∑ x ∈ F, (1 / Fintype.card α : ℝ) ^ (C x).length ≤ 1 := by
    intro F
    have h := InformationTheory.IsUniquelyDecodable.finsetSum_one_div_card_pow_length_le_one
      (S := F.image C) (isUniquelyDecodable_anti (by
        intro w hw
        rw [coe_image] at hw
        obtain ⟨x, -, rfl⟩ := hw
        exact ⟨x, rfl⟩) hud)
    rwa [sum_image fun x _ y _ hxy => hinj hxy] at h
  have hs := summable_of_sum_le (fun x => pow_nonneg (by positivity) _) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

/-- **Section 5.5.** Uniquely decodable codes offer no other choices of codeword lengths than
prefix codes. -/
theorem exists_prefixCode_iff_exists_uniquelyDecodableCode [Finite X] [Nontrivial X]
    [Finite α] [Nonempty α] (l : X → ℕ) :
    (∃ C : X → List α, IsPrefixCode C ∧ ∀ x, (C x).length = l x) ↔
      ∃ C : X → List α, IsUniquelyDecodableCode C ∧ ∀ x, (C x).length = l x := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite α
  constructor
  · rintro ⟨C, hC, hl⟩; exact ⟨C, hC.isUniquelyDecodableCode', hl⟩
  · rintro ⟨C, hC, hl⟩
    refine exists_prefixCode_of_kraft l ?_
    simpa [hl] using kraft_of_isUniquelyDecodableCode hC

end InfoTheory
