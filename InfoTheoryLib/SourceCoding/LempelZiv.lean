/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Nodup

/-!
# Lempel–Ziv coding

The Lempel–Ziv algorithms parse a string into phrases and replace each phrase by a pointer to an
earlier occurrence.

* **LZ77 (sliding window).** In the variant of Storer and Szymanski, the next phrase is the
  longest string starting at the current position that also starts in the window of the last
  `W` positions; it is sent as a pair `(P, L)` (the distance back to the match and its length),
  or as an uncompressed symbol if there is no match.
* **LZ78 (tree-structured).** The string is parsed into the shortest phrases not seen before.
  Every proper prefix of a phrase is an earlier phrase, so the phrase is sent as the index of
  the phrase obtained by dropping its last symbol, together with that last symbol.

## Main definitions

* `LZ77Token`, `lz77Encode W x`, `lz77Decode`: the sliding window algorithm.
* `lz78Parse x`: the incremental parsing, a list of distinct phrases and a final, possibly
  incomplete, phrase.
* `lz78Encode x`, `lz78Decode`: the tree-structured algorithm.
* `lz78Count x`, `lz78Length x`: the number `c(n)` of phrases and the length
  `c(n) (⌈log₂ c(n)⌉ + 1)` of the binary LZ78 code.

## Main statements

* `lz78Parse_flatten`: the phrases concatenate to the string.
* `lz78Parse_nodup`: **Section 13.4.2**, the parsing is distinct.
* `lz78Parse_prefixClosed`: the prefix of every phrase without its last symbol is an earlier
  phrase (or empty), so the phrases form a tree.
* `lz78Decode_encode`: the LZ78 code is decodable.

## Implementation notes

A string is a `List α`. The final phrase of the LZ78 parsing is a phrase seen before (or empty),
so it is sent as a pointer alone. Positions are counted from `0`, and LZ78 pointers from `1`, the
pointer `0` standing for the empty phrase. All algorithms are structurally recursive, so worked
examples can be checked by evaluation.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 13.4
-/

@[expose] public section

namespace InfoTheory

variable {α : Type*} [DecidableEq α]

/-! ### LZ77: sliding window Lempel–Ziv -/

/-- A token of the LZ77 code: an uncompressed symbol, or a pointer `(P, L)` to a match of length
`L` starting `P` positions back. -/
inductive LZ77Token (α : Type*)
  | literal : α → LZ77Token α
  | pointer : ℕ → ℕ → LZ77Token α
  deriving DecidableEq

/-- The length of the longest common prefix of two strings. -/
def lcpLength : List α → List α → ℕ
  | a :: as, b :: bs => if a = b then lcpLength as bs + 1 else 0
  | _, _ => 0

/-- The best match for position `i` in the window of the last `W` positions: the pair `(P, L)`
maximizing the match length `L` of `x_{i-P} x_{i-P+1} ⋯` with `xᵢ xᵢ₊₁ ⋯`, the most recent
match winning ties. Matches may overlap the current phrase. -/
def lz77Best (x : List α) (W i : ℕ) : ℕ × ℕ :=
  (List.range (min W i)).foldl (fun best d =>
    let L := lcpLength (x.drop (i - (d + 1))) (x.drop i)
    if best.2 < L then (d + 1, L) else best) (0, 0)

/-- The LZ77 parsing from position `i`, with `fuel` bounding the number of phrases. -/
def lz77Aux (x : List α) (W : ℕ) : ℕ → ℕ → List (LZ77Token α)
  | 0, _ => []
  | fuel + 1, i =>
    match x.drop i with
    | [] => []
    | a :: _ =>
      if (lz77Best x W i).2 = 0 then .literal a :: lz77Aux x W fuel (i + 1)
      else .pointer (lz77Best x W i).1 (lz77Best x W i).2 ::
        lz77Aux x W fuel (i + (lz77Best x W i).2)

/-- **Section 13.4.1** The LZ77 code of `x` with window size `W` (Storer–Szymanski). -/
def lz77Encode (W : ℕ) (x : List α) : List (LZ77Token α) := lz77Aux x W x.length 0

/-- Copy `L` symbols, each from `P` positions back, onto the decoded string. -/
def lz77Copy [Inhabited α] (P : ℕ) : ℕ → List α → List α
  | 0, out => out
  | L + 1, out => lz77Copy P L (out ++ [out.getD (out.length - P) default])

/-- The LZ77 decoder. -/
def lz77Decode [Inhabited α] : List (LZ77Token α) → List α → List α
  | [], out => out
  | .literal a :: ts, out => lz77Decode ts (out ++ [a])
  | .pointer P L :: ts, out => lz77Decode ts (lz77Copy P L out)

/-! ### LZ78: tree-structured Lempel–Ziv -/

/-- The incremental parsing: `dict` holds the phrases so far, `cur` the current phrase. A new
phrase ends as soon as it differs from all earlier phrases. -/
def lz78Aux : List (List α) → List α → List α → List (List α) × List α
  | dict, cur, [] => (dict, cur)
  | dict, cur, a :: rest =>
    if cur ++ [a] ∈ dict then lz78Aux dict (cur ++ [a]) rest
    else lz78Aux (dict ++ [cur ++ [a]]) [] rest

/-- **Section 13.4.2** The LZ78 parsing of `x` into the shortest phrases not seen before: the list
of phrases, and the final phrase, which has been seen before (or is empty). -/
def lz78Parse (x : List α) : List (List α) × List α := lz78Aux [] [] x

lemma lz78Aux_flatten (dict : List (List α)) (cur xs : List α) :
    (lz78Aux dict cur xs).1.flatten ++ (lz78Aux dict cur xs).2 = dict.flatten ++ cur ++ xs := by
  induction xs generalizing dict cur with
  | nil => simp [lz78Aux]
  | cons a rest ih =>
    rw [lz78Aux]
    split_ifs
    · rw [ih]
      simp
    · rw [ih]
      simp

/-- The phrases of the LZ78 parsing, followed by the final phrase, make up the string. -/
theorem lz78Parse_flatten (x : List α) : (lz78Parse x).1.flatten ++ (lz78Parse x).2 = x := by
  rw [lz78Parse, lz78Aux_flatten]
  simp

lemma lz78Aux_nodup {dict : List (List α)} (h : dict.Nodup) (cur xs : List α) :
    (lz78Aux dict cur xs).1.Nodup := by
  induction xs generalizing dict cur with
  | nil => exact h
  | cons a rest ih =>
    rw [lz78Aux]
    split_ifs with hmem
    · exact ih h _
    · refine ih ?_ _
      rw [← List.concat_eq_append]
      exact List.Nodup.concat hmem h

/-- **The LZ78 parsing is distinct**: no two phrases are equal. -/
theorem lz78Parse_nodup (x : List α) : (lz78Parse x).1.Nodup :=
  lz78Aux_nodup List.nodup_nil _ _

lemma lz78Aux_subset (dict : List (List α)) (cur xs : List α) :
    dict ⊆ (lz78Aux dict cur xs).1 := by
  induction xs generalizing dict cur with
  | nil => exact List.Subset.refl _
  | cons a rest ih =>
    rw [lz78Aux]
    split_ifs
    · exact ih _ _
    · exact fun w hw => ih _ _ (List.mem_append_left _ hw)

lemma lz78Aux_last {dict : List (List α)} {cur : List α} (h : cur = [] ∨ cur ∈ dict)
    (xs : List α) :
    (lz78Aux dict cur xs).2 = [] ∨ (lz78Aux dict cur xs).2 ∈ (lz78Aux dict cur xs).1 := by
  induction xs generalizing dict cur with
  | nil =>
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  | cons a rest ih =>
    rw [lz78Aux]
    split_ifs with hmem
    · exact ih (Or.inr hmem)
    · exact ih (Or.inl rfl)

/-- The final phrase of the LZ78 parsing is empty or one of the phrases. -/
theorem lz78Parse_last (x : List α) : (lz78Parse x).2 = [] ∨ (lz78Parse x).2 ∈ (lz78Parse x).1 :=
  lz78Aux_last (Or.inl rfl) x

/-- A list of phrases `ws`, following the phrases `D`, is prefix-closed if every phrase is
nonempty and its prefix without the last symbol is empty or an earlier phrase. -/
def PrefixClosed : List (List α) → List (List α) → Prop
  | _, [] => True
  | D, w :: ws => w ≠ [] ∧ (w.dropLast = [] ∨ w.dropLast ∈ D) ∧ PrefixClosed (D ++ [w]) ws

omit [DecidableEq α] in
lemma prefixClosed_append_singleton {D ws : List (List α)} (h : PrefixClosed D ws) {w : List α}
    (hw : w ≠ []) (hd : w.dropLast = [] ∨ w.dropLast ∈ D ++ ws) :
    PrefixClosed D (ws ++ [w]) := by
  induction ws generalizing D with
  | nil =>
    simp only [PrefixClosed, List.nil_append, List.append_nil] at hd ⊢
    exact ⟨hw, hd, trivial⟩
  | cons v ws ih =>
    obtain ⟨hv, hvd, hrest⟩ := h
    refine ⟨hv, hvd, ih hrest ?_⟩
    simpa using hd

lemma lz78Aux_prefixClosed {dict : List (List α)} {cur : List α} (hD : PrefixClosed [] dict)
    (h : cur = [] ∨ cur ∈ dict) (xs : List α) : PrefixClosed [] (lz78Aux dict cur xs).1 := by
  induction xs generalizing dict cur with
  | nil => exact hD
  | cons a rest ih =>
    rw [lz78Aux]
    split_ifs with hmem
    · exact ih hD (Or.inr hmem)
    · refine ih (prefixClosed_append_singleton hD (by simp) ?_) (Or.inl rfl)
      rw [List.dropLast_concat]
      simpa using h

/-- **The LZ78 phrases form a tree**: dropping the last symbol of a phrase gives an earlier phrase
(or the empty string). -/
theorem lz78Parse_prefixClosed (x : List α) : PrefixClosed [] (lz78Parse x).1 :=
  lz78Aux_prefixClosed (dict := []) trivial (Or.inl rfl) x

/-- The pointer to a phrase: its position (from `1`) in the list of phrases, or `0` for the empty
phrase. -/
def lz78Pointer (dict : List (List α)) (u : List α) : ℕ := if u = [] then 0 else dict.idxOf u + 1

/-- The phrase a pointer stands for. -/
def lz78Phrase (dict : List (List α)) (p : ℕ) : List α := if p = 0 then [] else dict.getD (p - 1) []

/-- **Section 13.4.2** The LZ78 code: each phrase is sent as the pointer to its prefix without the
last symbol, together with that symbol; the final phrase is sent as a pointer. -/
def lz78Encode [Inhabited α] (x : List α) : List (ℕ × α) × ℕ :=
  ((lz78Parse x).1.map fun w => (lz78Pointer (lz78Parse x).1 w.dropLast, w.getLast!),
    lz78Pointer (lz78Parse x).1 (lz78Parse x).2)

/-- The LZ78 decoder rebuilds the phrases one at a time. -/
def lz78DecodeAux : List (List α) → List (ℕ × α) → List (List α)
  | dict, [] => dict
  | dict, (p, a) :: ts => lz78DecodeAux (dict ++ [lz78Phrase dict p ++ [a]]) ts

/-- The LZ78 decoder. -/
def lz78Decode (c : List (ℕ × α) × ℕ) : List α :=
  (lz78DecodeAux [] c.1).flatten ++ lz78Phrase (lz78DecodeAux [] c.1) c.2

lemma lz78Phrase_pointer {dict : List (List α)} {u : List α} (h : u = [] ∨ u ∈ dict) :
    lz78Phrase dict (lz78Pointer dict u) = u := by
  rcases eq_or_ne u [] with hu | hu
  · simp [lz78Pointer, lz78Phrase, hu]
  · have hmem := h.resolve_left hu
    simp only [lz78Pointer, hu, ite_false, lz78Phrase, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hmem), List.getElem_idxOf]

lemma lz78Pointer_append {D : List (List α)} {u : List α} (h : u = [] ∨ u ∈ D)
    (E : List (List α)) : lz78Pointer (D ++ E) u = lz78Pointer D u := by
  rcases eq_or_ne u [] with hu | hu
  · simp [lz78Pointer, hu]
  · simp [lz78Pointer, hu, List.idxOf_append_of_mem (h.resolve_left hu)]

lemma lz78DecodeAux_map [Inhabited α] {D ws : List (List α)} (h : PrefixClosed D ws) :
    lz78DecodeAux D (ws.map fun w => (lz78Pointer (D ++ ws) w.dropLast, w.getLast!)) = D ++ ws := by
  induction ws generalizing D with
  | nil => simp [lz78DecodeAux]
  | cons w ws ih =>
    obtain ⟨hw, hd, hrest⟩ := h
    rw [List.map_cons, lz78DecodeAux, lz78Pointer_append hd, lz78Phrase_pointer hd,
      List.getLast!_of_getLast? (List.getLast?_eq_some_getLast hw), List.dropLast_append_getLast hw]
    have := ih hrest
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this
    exact this

/-- **The LZ78 code is decodable.** -/
theorem lz78Decode_encode [Inhabited α] (x : List α) : lz78Decode (lz78Encode x) = x := by
  have h := lz78DecodeAux_map (D := []) (lz78Parse_prefixClosed x)
  simp only [List.nil_append] at h
  rw [lz78Decode, lz78Encode, h]
  have hl := lz78Parse_last x
  rw [lz78Phrase_pointer hl]
  exact lz78Parse_flatten x

/-- The number `c(n)` of phrases of the LZ78 parsing, the final phrase included. -/
def lz78Count (x : List α) : ℕ := (lz78Parse x).1.length + if (lz78Parse x).2 = [] then 0 else 1

/-- The length `c(n) (⌈log₂ c(n)⌉ + 1)` of the binary LZ78 code: each phrase costs a pointer of
`⌈log₂ c(n)⌉` bits and one bit for its last symbol. -/
def lz78Length (x : List α) : ℕ := lz78Count x * (Nat.clog 2 (lz78Count x) + 1)

end InfoTheory
