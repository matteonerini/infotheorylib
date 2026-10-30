/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Probability.FinitePMF
public import Mathlib.InformationTheory.Coding.Kraft

/-!
# Source codes

A source code for a random variable `X` with values in `𝒳` maps each symbol `x` to a codeword
`C(x)`, a finite string over a `D`-ary code alphabet `α` (with `D = |α|`). Codewords are
`List α`.

## Main definitions

* `expectedLength p C`: the expected length `L(C) = ∑ₓ p(x) l(x)` of a code, (5.1).
* `IsNonsingular C`: distinct symbols have distinct codewords, (5.4).
* `extension C`: the extension `C*(x₁ ⋯ xₙ) = C(x₁) ⋯ C(xₙ)`, (5.5).
* `IsUniquelyDecodableCode C`: the extension is non-singular.
* `IsPrefixCode C`: no codeword is a prefix of another (an instantaneous code).

## Main statements

* `IsPrefixCode.isUniquelyDecodableCode`, `IsUniquelyDecodableCode.isNonsingular`: every
  instantaneous code is uniquely decodable, and every uniquely decodable code is non-singular
  (Figure 5.1).
* `isPrefixCode_iff`, `isUniquelyDecodableCode_iff`: the connection with Mathlib's
  `InformationTheory.IsPrefixFree` and `InformationTheory.IsUniquelyDecodable` for sets of
  codewords.

## References

* [T. M. Cover and J. A. Thomas, *Elements of Information Theory*][cover2006], Section 5.1
-/

open Finset

@[expose] public noncomputable section

namespace InfoTheory

variable {X α : Type*}

/-- **Definition (5.1).** The expected length `L(C) = ∑ₓ p(x) l(x)` of a code `C`. -/
def expectedLength [Fintype X] (p : X → ℝ) (C : X → List α) : ℝ := ∑ x, p x * (C x).length

/-- **Definition (5.4).** A code is non-singular if distinct symbols have distinct codewords. -/
def IsNonsingular (C : X → List α) : Prop := Function.Injective C

/-- **Definition (5.5).** The extension `C*(x₁ x₂ ⋯ xₙ) = C(x₁) C(x₂) ⋯ C(xₙ)` of a code. -/
def extension (C : X → List α) (xs : List X) : List α := (xs.map C).flatten

/-- **Definition.** A code is uniquely decodable if its extension is non-singular. -/
def IsUniquelyDecodableCode (C : X → List α) : Prop := Function.Injective (extension C)

/-- **Definition.** A code is a prefix code (an instantaneous code) if no codeword is a prefix of
any other codeword. -/
def IsPrefixCode (C : X → List α) : Prop := ∀ x y, C x <+: C y → x = y

@[simp] lemma extension_nil (C : X → List α) : extension C [] = [] := rfl

@[simp] lemma extension_cons (C : X → List α) (x : X) (xs : List X) :
    extension C (x :: xs) = C x ++ extension C xs := by
  simp [extension]

lemma extension_append (C : X → List α) (xs ys : List X) :
    extension C (xs ++ ys) = extension C xs ++ extension C ys := by
  simp [extension]

/-- **Example 5.1.4.** The extension concatenates the codewords: `C*(x₁ x₂) = C(x₁) C(x₂)`. -/
lemma extension_pair (C : X → List α) (x₁ x₂ : X) : extension C [x₁, x₂] = C x₁ ++ C x₂ := by
  simp [extension]

lemma IsPrefixCode.injective {C : X → List α} (hC : IsPrefixCode C) : Function.Injective C :=
  fun x y h => hC x y (h ▸ List.prefix_refl _)

/-- A prefix code is non-singular. -/
lemma IsPrefixCode.isNonsingular {C : X → List α} (hC : IsPrefixCode C) : IsNonsingular C :=
  hC.injective

/-- A uniquely decodable code is non-singular. -/
lemma IsUniquelyDecodableCode.isNonsingular {C : X → List α} (hC : IsUniquelyDecodableCode C) :
    IsNonsingular C := fun x y h => by
  have : extension C [x] = extension C [y] := by simp [extension, h]
  simpa using hC this

/-- A prefix code is prefix-free as a set of codewords, and conversely for injective codes. -/
lemma isPrefixCode_iff {C : X → List α} :
    IsPrefixCode C ↔ Function.Injective C ∧ InformationTheory.IsPrefixFree (Set.range C) := by
  constructor
  · intro hC
    refine ⟨hC.injective, ?_⟩
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
    rw [hC x y h]
  · rintro ⟨hinj, hpf⟩ x y h
    exact hinj (hpf _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h)

lemma exists_map_eq_of_forall_mem_range {C : X → List α} :
    ∀ L : List (List α), (∀ w ∈ L, w ∈ Set.range C) → ∃ xs : List X, xs.map C = L
  | [], _ => ⟨[], rfl⟩
  | w :: L, h => by
    obtain ⟨x, hx⟩ := h w (List.mem_cons_self ..)
    obtain ⟨xs, hxs⟩ :=
      exists_map_eq_of_forall_mem_range L fun v hv => h v (List.mem_cons_of_mem _ hv)
    exact ⟨x :: xs, by simp [hx, hxs]⟩

/-- A code is uniquely decodable iff it is injective and its set of codewords is uniquely
decodable in the sense of `InformationTheory.IsUniquelyDecodable`. -/
lemma isUniquelyDecodableCode_iff {C : X → List α} :
    IsUniquelyDecodableCode C ↔
      Function.Injective C ∧ InformationTheory.IsUniquelyDecodable (Set.range C) := by
  constructor
  · intro hC
    refine ⟨hC.isNonsingular, fun L₁ L₂ h₁ h₂ h => ?_⟩
    obtain ⟨xs₁, rfl⟩ := exists_map_eq_of_forall_mem_range L₁ h₁
    obtain ⟨xs₂, rfl⟩ := exists_map_eq_of_forall_mem_range L₂ h₂
    rw [hC h]
  · rintro ⟨hinj, hud⟩ xs ys h
    have := hud (xs.map C) (ys.map C) (by simp) (by simp) h
    exact List.map_injective_iff.2 hinj this

/-- **Figure 5.1.** Every instantaneous code with nonempty codewords is uniquely decodable. -/
theorem IsPrefixCode.isUniquelyDecodableCode {C : X → List α} (hC : IsPrefixCode C)
    (hne : ∀ x, C x ≠ []) : IsUniquelyDecodableCode C := by
  rw [isUniquelyDecodableCode_iff]
  refine ⟨hC.injective, (isPrefixCode_iff.1 hC).2.isUniquelyDecodable ?_⟩
  rintro ⟨x, hx⟩
  exact hne x hx

/-- In a prefix code for at least two symbols, every codeword is nonempty. -/
lemma IsPrefixCode.ne_nil [Nontrivial X] {C : X → List α} (hC : IsPrefixCode C) (x : X) :
    C x ≠ [] := by
  intro h
  obtain ⟨y, hy⟩ := exists_ne x
  exact hy (hC x y (h ▸ List.nil_prefix)).symm

/-- **Figure 5.1.** Every instantaneous code for at least two symbols is uniquely decodable. -/
theorem IsPrefixCode.isUniquelyDecodableCode' [Nontrivial X] {C : X → List α}
    (hC : IsPrefixCode C) : IsUniquelyDecodableCode C :=
  hC.isUniquelyDecodableCode hC.ne_nil

end InfoTheory
