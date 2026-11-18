/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.NoiselessCode

/-!
# Forwarding at a node with one input channel

A node `k` without a message of its own whose only input channel comes from `j` needs no coding:
if each output channel of `k` can carry the symbol received from `j`, a code can be changed so that
`k` forwards that symbol on every output channel, and each receiving node `l` applies the function
`gₗ` that `k` used to apply. Every node then decodes exactly as before (Proposition 17.3).

## Main definitions

* `NetCode.forward`: the code in which node `k` forwards its input.

## Main statements

* `NetCode.forward_edge_self`, `NetCode.forward_out`: **Proposition 17.3**.

## Implementation notes

Since `NetCode` gives every pair `i < k` an alphabet `A i k`, "only one input channel" means that
the alphabets of the pairs `(i, k)` with `i ≠ j` are subsingletons, as the one-element alphabets of
the pairs that are not edges in a `RateCode`. That an output channel has the capacity of the input
channel is weakened to: its alphabet holds a copy of the input alphabet, through `s l` with left
inverse `r l`.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Section 17.2
-/

@[expose] public noncomputable section

namespace InfoTheory

variable {V : Type*} [LinearOrder V] {A : V → V → Type*} {M : V → Type*}

namespace NetCode

section Forward

variable (c : NetCode V A M) {j k : V} (hjk : j < k) [∀ i, Nonempty (A i k)] [Nonempty (M k)]
  (r : ∀ l, A k l → A j k) (s : ∀ l, A j k → A k l)

/-- The inputs of node `k` when it receives `x` from `j`: the other inputs carry their only
symbol. -/
def fwdInputs (x : A j k) : ∀ i, i < k → A i k :=
  fun i _ => if h : i = j then h ▸ x else Classical.arbitrary _

/-- The inputs that node `l` would receive in the code `c`, rebuilt from its inputs in the
forwarding code: the symbol `y` from `k` is replaced by `gₗ (r y)`, what `k` sends to `l` in `c`. -/
def unfwd (l : V) (u : ∀ i, i < l → A i l) : ∀ i, i < l → A i l :=
  fun i h => if hik : i = k then hik ▸ c.enc k l (fwdInputs (r l (hik ▸ u i h)))
    (Classical.arbitrary _) else u i h

/-- The encoder of node `i` in the forwarding code. -/
def fwdEnc (i l : V) (u : ∀ i', i' < i → A i' i) (mi : M i) : A i l :=
  if hi : i = k then by subst hi; exact s l (u j hjk) else c.enc i l (c.unfwd r i u) mi

/-- **Proposition 17.3.** The code in which node `k` forwards the symbol received from `j` on every
output channel, and every other node first rebuilds the inputs it would receive in `c`. -/
def forward : NetCode V A M where
  enc := c.fwdEnc hjk r s
  dec l i u := c.dec l i (c.unfwd r l u)

lemma fwdEnc_self (l : V) (u : ∀ i', i' < k → A i' k) (mk : M k) :
    c.fwdEnc hjk r s k l u mk = s l (u j hjk) := by
  simp [fwdEnc]

lemma fwdEnc_of_ne {i : V} (hi : i ≠ k) (l : V) (u : ∀ i', i' < i → A i' i) (mi : M i) :
    c.fwdEnc hjk r s i l u mi = c.enc i l (c.unfwd r i u) mi := by
  simp [fwdEnc, hi]

lemma unfwd_self (l : V) (u : ∀ i, i < l → A i l) (h : k < l) :
    c.unfwd r l u k h = c.enc k l (fwdInputs (r l (u k h))) (Classical.arbitrary _) := by
  simp [unfwd]

lemma unfwd_of_ne (l : V) (u : ∀ i, i < l → A i l) {i : V} (h : i < l) (hi : i ≠ k) :
    c.unfwd r l u i h = u i h := by
  simp [unfwd, hi]

variable [Finite V] [Subsingleton (M k)] (hin : ∀ i, i ≠ j → Subsingleton (A i k))
include hin

omit [Nonempty (M k)] [Subsingleton (M k)] in
/-- The inputs of `k` in `c` are those rebuilt from the symbol received from `j`, since the other
inputs of `k` carry a single symbol. -/
lemma fwdInputs_edge (m : ∀ i, M i) :
    fwdInputs (c.edge m j k) = fun i (_ : i < k) => c.edge m i k := by
  funext i h
  by_cases hij : i = j
  · subst hij
    simp [fwdInputs]
  · have := hin i hij
    exact Subsingleton.elim _ _

/-- The symbol that `k` sends to `l` in `c`, from the symbol it receives from `j`. -/
lemma enc_fwdInputs (m : ∀ i, M i) (l : V) :
    c.enc k l (fwdInputs (c.edge m j k)) (Classical.arbitrary _) = c.edge m k l := by
  rw [fwdInputs_edge c hin, Subsingleton.elim (Classical.arbitrary (M k)) (m k), ← edge_eq]

/-- In the forwarding code, the nodes other than `k` send what they send in `c`. -/
lemma forward_edge_of_ne (hrs : ∀ l x, r l (s l x) = x) (m : ∀ i, M i) :
    ∀ i, i ≠ k → ∀ l, (c.forward hjk r s).edge m i l = c.edge m i l := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro hi l
    rw [edge_eq, edge_eq c]
    change c.fwdEnc hjk r s i l _ (m i) = _
    rw [fwdEnc_of_ne c hjk r s hi]
    congr 1
    funext i' h
    by_cases hi' : i' = k
    · subst hi'
      rw [unfwd_self, edge_eq, ← enc_fwdInputs c hin m i]
      change c.enc i' i (fwdInputs (r i (c.fwdEnc hjk r s i' i _ (m i')))) _ = _
      rw [fwdEnc_self, ih j (hjk.trans h) hjk.ne, hrs]
    · rw [unfwd_of_ne c r i _ h hi', ih i' h hi']

/-- **Proposition 17.3.** In the forwarding code, `k` sends on each output channel the symbol it
receives from `j`. -/
theorem forward_edge_self (hrs : ∀ l x, r l (s l x) = x) (m : ∀ i, M i) (l : V) :
    (c.forward hjk r s).edge m k l = s l (c.edge m j k) := by
  rw [edge_eq]
  change c.fwdEnc hjk r s k l _ (m k) = _
  rw [fwdEnc_self, c.forward_edge_of_ne hjk r s hin hrs m j hjk.ne]

/-- The rebuilt inputs of every node are its inputs in `c`. -/
lemma unfwd_forward (hrs : ∀ l x, r l (s l x) = x) (m : ∀ i, M i) (l : V) :
    c.unfwd r l (fun i _ => (c.forward hjk r s).edge m i l) = fun i _ => c.edge m i l := by
  funext i h
  by_cases hi : i = k
  · subst hi
    rw [unfwd_self, forward_edge_self c hjk r s hin hrs, hrs, enc_fwdInputs c hin]
  · rw [unfwd_of_ne c r l _ h hi, forward_edge_of_ne c hjk r s hin hrs m i hi]

/-- **Proposition 17.3.** Every node decodes in the forwarding code exactly as in `c`, so network
coding is not needed at `k`. -/
theorem forward_out (hrs : ∀ l x, r l (s l x) = x) (m : ∀ i, M i) (l i : V) :
    (c.forward hjk r s).out m l i = c.out m l i := by
  change c.dec l i (c.unfwd r l fun i _ => (c.forward hjk r s).edge m i l) = _
  rw [unfwd_forward c hjk r s hin hrs]
  rfl

end Forward

end NetCode

end InfoTheory
