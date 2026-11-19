/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ForMathlib.MaxFlow

/-!
# The max-flow bound for network codes

A point-to-point communication network is a finite directed multigraph, possibly with cycles, whose
edges carry a given integer number of symbols per unit time. A network code sends, in `K`
transactions in chronological order, a symbol on an edge, computed by the tail of the edge from what
it has received so far; only the source sees the message. If every sink decodes the message, the
rate is at most the max-flow from the source to every sink (Theorem 18.3).

## Main definitions

* `PtpNetwork V E`: a network with nodes `V`, edges `E` and capacities `cap`.
* `PtpNetwork.capMatrix`, `PtpNetwork.maxflow`: the capacities between nodes, summed over parallel
  edges, and the value of a max-flow.
* `PtpNetwork.TransCode`: the network codes of Section 18.3.
* `PtpNetwork.IsAchievableInfoRate`: Definition 18.2.

## Main statements

* `PtpNetwork.isGreatest_maxflow`: **Theorem 18.1**, the max-flow min-cut theorem.
* `PtpNetwork.TransCode.card_le_prod_eta`: a code multicasts at most `∏_{e ∈ E_U} ηₑ` messages
  across a cut `U`.
* `PtpNetwork.IsAchievableInfoRate.le_maxflow`: **Theorem 18.3**, the max-flow bound.
* `PtpNetwork.isAchievableInfoRate_of_code`: a code for one unit of time gives an achievable rate.

## Implementation notes

The book proves (18.34)–(18.40) with entropies. Here the same chain is a count: two messages whose
symbols agree on the transactions across a cut agree on every transaction into a node beyond the
cut, so a sink beyond it tells them apart only if they differ on the cut.

A transaction carries a symbol of any finite alphabet `A k`, in place of the book's index set
`{1, …, |A k|}`, and the source may also receive symbols. Flows are on the matrix of capacities
between nodes, so parallel edges are merged.

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 18
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-- **Section 18.1.** A point-to-point communication network: a finite directed multigraph whose
edge `e` goes from `tail e` to `head e` and carries `cap e` symbols per unit time. -/
structure PtpNetwork (V E : Type*) where
  /-- The node an edge leaves. -/
  tail : E → V
  /-- The node an edge enters. -/
  head : E → V
  /-- The rate constraint of an edge. -/
  cap : E → ℕ

namespace PtpNetwork

variable {V E : Type*} (G : PtpNetwork V E)

/-! ### Flows and cuts -/

section Cuts

variable [Fintype V] [DecidableEq V] [Fintype E]

/-- The capacity from node `i` to node `j`: the sum of the rate constraints of the edges from `i`
to `j`. -/
def capMatrix (i j : V) : ℝ := ∑ e with G.tail e = i ∧ G.head e = j, (G.cap e : ℝ)

omit [Fintype V] in
lemma capMatrix_nonneg (i j : V) : 0 ≤ G.capMatrix i j :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- The edges across the cut `U`, (18.7). -/
def cutEdges (U : Finset V) : Finset E := univ.filter fun e => G.tail e ∈ U ∧ G.head e ∉ U

/-- The capacity of the cut `U`, (18.8), is the cut capacity of `capMatrix`. -/
lemma cutCap_capMatrix (U : Finset V) :
    cutCap G.capMatrix U = ∑ e ∈ G.cutEdges U, (G.cap e : ℝ) := by
  classical
  simp only [cutCap, capMatrix, cutEdges, sum_filter]
  calc ∑ j ∈ U, ∑ k ∈ Uᶜ, ∑ e, (if G.tail e = j ∧ G.head e = k then (G.cap e : ℝ) else 0)
      = ∑ j ∈ U, ∑ e, ∑ k ∈ Uᶜ, (if G.tail e = j ∧ G.head e = k then (G.cap e : ℝ) else 0) :=
        sum_congr rfl fun _ _ => sum_comm
    _ = ∑ e, ∑ j ∈ U, ∑ k ∈ Uᶜ, (if G.tail e = j ∧ G.head e = k then (G.cap e : ℝ) else 0) :=
        sum_comm
    _ = _ := sum_congr rfl fun e _ => by
        simp only [ite_and]
        rw [sum_congr rfl fun x _ => (sum_ite_irrel _ _ _ _).trans (by rw [sum_const_zero]),
          sum_ite_eq, sum_ite_eq]
        simp only [mem_compl]

/-- The value of a max-flow from `s` to `t`: the capacity of a min-cut, by Theorem 18.1. -/
def maxflow (s t : V) : ℝ := minCut G.capMatrix s t

/-- **Theorem 18.1 (Max-Flow Min-Cut Theorem).** The value of a max-flow from `s` to `t` is the
capacity of a min-cut between `s` and `t`. -/
theorem isGreatest_maxflow {s t : V} (hst : s ≠ t) :
    IsGreatest {v | ∃ f, IsFlow G.capMatrix s t f v} (G.maxflow s t) :=
  maxFlow_minCut G.capMatrix_nonneg hst

/-- The max-flow is at most the capacity of any cut. -/
lemma maxflow_le {s t : V} {U : Finset V} (hs : s ∈ U) (ht : t ∉ U) :
    G.maxflow s t ≤ ∑ e ∈ G.cutEdges U, (G.cap e : ℝ) := by
  rw [← cutCap_capMatrix]
  exact minCut_le _ hs ht

end Cuts

/-! ### Network codes -/

/-- **Section 18.3.** A network code that multicasts a message `x ∈ X` from `s` to the sinks `T`. In
the `k`-th of `K` transactions, the tail of the edge `edge k` sends to its head a symbol of the
finite alphabet `A k`. The symbol is computed by the encoder `enc k` from the message, which only
`s` may use, and from the symbols that the tail received in earlier transactions. Each sink `t`
decodes with `dec t` from the symbols it receives. -/
structure TransCode (s : V) (X : Type*) (T : Finset V) where
  /-- The number of transactions. -/
  K : ℕ
  /-- The edge used by each transaction. -/
  edge : Fin K → E
  /-- The alphabet of each transaction. -/
  A : Fin K → Type
  /-- The alphabets are finite. -/
  fintype : ∀ k, Fintype (A k)
  /-- The encoder of each transaction. -/
  enc : ∀ k, X → (∀ k' : Fin K, k' < k → G.head (edge k') = G.tail (edge k) → A k') → A k
  /-- Only the source sees the message. -/
  enc_eq : ∀ k, G.tail (edge k) ≠ s → ∀ x x' u, enc k x u = enc k x' u
  /-- The decoder of each sink. -/
  dec : ∀ t ∈ T, (∀ k, G.head (edge k) = t → A k) → X

attribute [instance] TransCode.fintype

namespace TransCode

variable {G} {s : V} {X : Type*} {T : Finset V} (c : G.TransCode s X T)

/-- The symbol sent in transaction `k` when the message is `x`: the function `f̃ₖ` of the book. -/
def val (c : G.TransCode s X T) (x : X) (k : Fin c.K) : c.A k :=
  c.enc k x fun k' _ _ => val c x k'
termination_by (wellFounded_lt (α := Fin c.K)).wrap k
decreasing_by assumption

lemma val_eq (x : X) (k : Fin c.K) : c.val x k = c.enc k x fun k' _ _ => c.val x k' := by
  rw [val]

/-- Every sink decodes every message: (18.27). -/
def Correct : Prop := ∀ t (ht : t ∈ T) x, c.dec t ht (fun k _ => c.val x k) = x

/-- The number `ηₑ` of tuples of symbols that the code can send on the edge `e`, (18.19). -/
def eta [DecidableEq E] (e : E) : ℕ := ∏ k with c.edge k = e, Fintype.card (c.A k)

/-- Two messages whose symbols agree on the transactions across a cut `U` containing `s` agree on
every transaction into a node outside `U` (Problem 3). -/
lemma val_congr {U : Finset V} (hs : s ∈ U) {x x' : X}
    (h : ∀ k, G.tail (c.edge k) ∈ U → G.head (c.edge k) ∉ U → c.val x k = c.val x' k) :
    ∀ k, G.head (c.edge k) ∉ U → c.val x k = c.val x' k := by
  intro k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    intro hk
    by_cases hu : G.tail (c.edge k) ∈ U
    · exact h k hu hk
    · have hks : G.tail (c.edge k) ≠ s := fun h => hu (by rw [h]; exact hs)
      rw [val_eq, val_eq, c.enc_eq k hks x x']
      congr 1
      funext k' h₁ h₂
      exact ih k' h₁ (by rw [h₂]; exact hu)

/-- **(18.34)–(18.40)** A code that is correct for a sink `t` outside a cut `U` containing `s` has
at most `∏_{e ∈ E_U} ηₑ` messages. -/
theorem card_le_prod_eta [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype X] (hc : c.Correct)
    {t : V} (ht : t ∈ T) {U : Finset V} (hs : s ∈ U) (htU : t ∉ U) :
    Fintype.card X ≤ ∏ e ∈ G.cutEdges U, c.eta e := by
  classical
  let φ : X → ∀ k : {k : Fin c.K // c.edge k ∈ G.cutEdges U}, c.A k.val := fun x k => c.val x k.val
  have hinj : Function.Injective φ := by
    intro x x' hxx
    have hcut : ∀ k, G.tail (c.edge k) ∈ U → G.head (c.edge k) ∉ U → c.val x k = c.val x' k :=
      fun k h₁ h₂ => congrFun hxx ⟨k, by simp [cutEdges, h₁, h₂]⟩
    rw [← hc t ht x, ← hc t ht x']
    congr 1
    funext k hk
    exact c.val_congr hs hcut k (by rw [hk]; exact htU)
  calc Fintype.card X ≤ Fintype.card (∀ k : {k : Fin c.K // c.edge k ∈ G.cutEdges U}, c.A k.val) :=
        Fintype.card_le_of_injective φ hinj
    _ = ∏ k : {k : Fin c.K // c.edge k ∈ G.cutEdges U}, Fintype.card (c.A k.val) :=
        Fintype.card_pi
    _ = ∏ k with c.edge k ∈ G.cutEdges U, Fintype.card (c.A k) :=
        (prod_subtype _ (by simp) fun k => Fintype.card (c.A k)).symm
    _ = ∏ e ∈ G.cutEdges U, c.eta e :=
        (prod_fiberwise_of_maps_to (fun k hk => (mem_filter.1 hk).2) _).symm.trans
          (prod_congr rfl fun e _ => by
            rw [eta, filter_filter]
            congr 1
            ext k
            simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
            rintro rfl
            assumption)

/-! ### Repetition and relabelling -/

/-- The code `c` used `n` times, on the `n` letters of a message in `Xⁿ`. -/
def pow (n : ℕ) : G.TransCode s (Fin n → X) T where
  K := c.K
  edge := c.edge
  A k := Fin n → c.A k
  fintype _ := inferInstance
  enc k x u := fun i => c.enc k (x i) fun k' h₁ h₂ => u k' h₁ h₂ i
  enc_eq k hk _ _ _ := funext fun _ => c.enc_eq k hk _ _ _
  dec t ht u := fun i => c.dec t ht fun k h => u k h i

lemma val_pow (n : ℕ) (x : Fin n → X) (k : Fin c.K) :
    (c.pow n).val x k = fun i => c.val (x i) k := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    refine (val_eq (c.pow n) x k).trans (funext fun i => ?_)
    refine Eq.trans ?_ (val_eq c (x i) k).symm
    change c.enc k (x i) (fun k' h₁ h₂ => (c.pow n).val x k' i) = _
    congr 1
    funext k' h₁ h₂
    rw [ih k' h₁]

lemma Correct.pow {c : G.TransCode s X T} (hc : c.Correct) (n : ℕ) : (c.pow n).Correct := by
  intro t ht x
  funext i
  change c.dec t ht (fun k h => (c.pow n).val x k i) = x i
  simp only [val_pow]
  exact hc t ht (x i)

lemma eta_pow [DecidableEq E] (n : ℕ) (e : E) : (c.pow n).eta e = c.eta e ^ n := by
  change ∏ k ∈ univ.filter (fun k : Fin c.K => c.edge k = e), Fintype.card (Fin n → c.A k) = _
  simp only [Fintype.card_fun, Fintype.card_fin, eta, prod_pow]

/-- The code `c` with its messages relabelled by `φ`. -/
def mapMsg {X' : Type*} (φ : X' ≃ X) : G.TransCode s X' T where
  K := c.K
  edge := c.edge
  A := c.A
  fintype := c.fintype
  enc k x u := c.enc k (φ x) u
  enc_eq k hk _ _ _ := c.enc_eq k hk _ _ _
  dec t ht u := φ.symm (c.dec t ht u)

lemma val_mapMsg {X' : Type*} (φ : X' ≃ X) (x : X') (k : Fin c.K) :
    (c.mapMsg φ).val x k = c.val (φ x) k := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    refine (val_eq (c.mapMsg φ) x k).trans (Eq.trans ?_ (val_eq c (φ x) k).symm)
    change c.enc k (φ x) (fun k' h₁ h₂ => (c.mapMsg φ).val x k') = _
    congr 1
    funext k' h₁ h₂
    exact ih k' h₁

lemma Correct.mapMsg {c : G.TransCode s X T} (hc : c.Correct) {X' : Type*} (φ : X' ≃ X) :
    (c.mapMsg φ).Correct := by
  intro t ht x
  change φ.symm (c.dec t ht fun k _ => (c.mapMsg φ).val x k) = x
  simp only [val_mapMsg]
  rw [hc t ht (φ x), Equiv.symm_apply_apply]

/-! ### Codes over one alphabet -/

section OfFun

variable [DecidableEq V] {Ω : Type} [Fintype Ω] [Zero Ω]

/-- A code over one alphabet `Ω`, given by functions `f k x w` of the message `x` and of the symbols
`w k'` of all transactions, of which only the earlier transactions into the tail of `edge k` are
passed (the others are `0`), and by decoders `g t w` that see the transactions into `t`. -/
def ofFun (K : ℕ) (edge : Fin K → E) (f : Fin K → X → (Fin K → Ω) → Ω)
    (hf : ∀ k, G.tail (edge k) ≠ s → ∀ x x' w, f k x w = f k x' w)
    (g : ∀ t ∈ T, (Fin K → Ω) → X) : G.TransCode s X T where
  K := K
  edge := edge
  A _ := Ω
  fintype _ := inferInstance
  enc k x u := f k x fun k' => if h : k' < k ∧ G.head (edge k') = G.tail (edge k) then
    u k' h.1 h.2 else 0
  enc_eq k hk x x' _ := hf k hk x x' _
  dec t ht u := g t ht fun k' => if h : G.head (edge k') = t then u k' h else 0

variable {K : ℕ} {edge : Fin K → E} {f : Fin K → X → (Fin K → Ω) → Ω}
  {hf : ∀ k, G.tail (edge k) ≠ s → ∀ x x' w, f k x w = f k x' w} {g : ∀ t ∈ T, (Fin K → Ω) → X}

/-- The symbols of a code over one alphabet are the solution `φ` of its recursion. -/
lemma val_ofFun (φ : Fin K → X → Ω) (hφ : ∀ k x, φ k x = f k x fun k' =>
      if k' < k ∧ G.head (edge k') = G.tail (edge k) then φ k' x else 0) (x : X) (k : Fin K) :
    (ofFun (G := G) K edge f hf g).val x k = φ k x := by
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    refine (val_eq (ofFun (G := G) K edge f hf g) x k).trans ?_
    rw [hφ]
    change f k x _ = _
    congr 1
    funext k'
    by_cases h : k' < k ∧ G.head (edge k') = G.tail (edge k)
    · simp only [h, and_self, ↓reduceDIte, ↓reduceIte]
      exact ih k' h.1
    · simp only [h, ↓reduceDIte, ↓reduceIte]

/-- A code over one alphabet is correct if its decoders recover the message from the solution `φ` of
its recursion. -/
lemma correct_ofFun (φ : Fin K → X → Ω) (hφ : ∀ k x, φ k x = f k x fun k' =>
      if k' < k ∧ G.head (edge k') = G.tail (edge k) then φ k' x else 0)
    (hg : ∀ t (ht : t ∈ T) x, g t ht (fun k' => if G.head (edge k') = t then φ k' x else 0) = x) :
    (ofFun (G := G) K edge f hf g).Correct := by
  intro t ht x
  change g t ht _ = x
  convert hg t ht x using 2
  funext k'
  by_cases h : G.head (edge k') = t
  · simp only [h, ↓reduceDIte, ↓reduceIte]
    exact val_ofFun φ hφ x k'
  · simp only [h, ↓reduceDIte, ↓reduceIte]

lemma eta_ofFun [DecidableEq E] (e : E) :
    (ofFun (G := G) K edge f hf g).eta e = Fintype.card Ω ^ #{k | edge k = e} := by
  rw [eta, ← prod_const]
  rfl

end OfFun

end TransCode

/-! ### The max-flow bound -/

section Bound

variable [DecidableEq E]

/-- **Definition 18.2.** A rate `ω` is (asymptotically) achievable if for every `ε > 0` and every
`n` sufficiently large there is a correct code with block length `n`, `⌈2^{nτ}⌉` messages for some
`τ ≥ ω - ε`, and `n⁻¹ log₂ ηₑ ≤ Rₑ + ε` on every edge, (18.28)–(18.29). -/
def IsAchievableInfoRate (s : V) (T : Finset V) (ω : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ τ : ℝ, ω - ε ≤ τ ∧
    ∃ c : G.TransCode s (Fin ⌈(2 : ℝ) ^ ((n : ℝ) * τ)⌉₊) T, c.Correct ∧
      ∀ e, logb 2 (c.eta e) ≤ n * (G.cap e + ε)

variable {G} {s : V} {T : Finset V}

/-- **The remark after Definition 18.2.** A smaller rate is achievable. -/
lemma IsAchievableInfoRate.mono {ω ω' : ℝ} (h : G.IsAchievableInfoRate s T ω) (hω : ω' ≤ ω) :
    G.IsAchievableInfoRate s T ω' := fun ε hε =>
  (h ε hε).mono fun _ ⟨τ, hτ, hc⟩ => ⟨τ, by linarith, hc⟩

/-- **The remark after Definition 18.2 (Problem 2a).** The set of achievable rates is closed. -/
theorem isClosed_setOf_isAchievableInfoRate : IsClosed {ω | G.IsAchievableInfoRate s T ω} := by
  refine isClosed_of_closure_subset fun ω hω ε hε => ?_
  obtain ⟨ω', hω', hd⟩ := Metric.mem_closure_iff.1 hω (ε / 2) (half_pos hε)
  rw [Real.dist_eq, abs_lt] at hd
  refine (hω' (ε / 2) (half_pos hε)).mono fun n ⟨τ, hτ, c, hc, hη⟩ => ⟨τ, by linarith, c, hc,
    fun e => (hη e).trans ?_⟩
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- **Theorem 18.3 (Max-Flow Bound).** An achievable rate is at most the max-flow from the source to
every sink, (18.30). -/
theorem IsAchievableInfoRate.le_maxflow [Fintype V] [DecidableEq V] [Fintype E] {ω : ℝ}
    (h : G.IsAchievableInfoRate s T ω) {t : V} (ht : t ∈ T) (hst : s ≠ t) :
    ω ≤ G.maxflow s t := by
  obtain ⟨U, hs, htU, hU⟩ := exists_cut_eq_minCut G.capMatrix hst
  rw [maxflow, ← hU, cutCap_capMatrix]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / (Fintype.card E + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨n, ⟨τ, hτ, c, hc, hη⟩, hn⟩ := ((h δ hδ0).and (eventually_ge_atTop 1)).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- the count (18.34)–(18.40)
  have hcard := c.card_le_prod_eta hc ht hs htU
  rw [Fintype.card_fin] at hcard
  have hpow : (2 : ℝ) ^ ((n : ℝ) * τ) ≤ ∏ e ∈ G.cutEdges U, (c.eta e : ℝ) := by
    calc (2 : ℝ) ^ ((n : ℝ) * τ) ≤ ⌈(2 : ℝ) ^ ((n : ℝ) * τ)⌉₊ := Nat.le_ceil _
      _ ≤ ∏ e ∈ G.cutEdges U, (c.eta e : ℝ) := by exact_mod_cast hcard
  have hpos : ∀ e ∈ G.cutEdges U, (0 : ℝ) < c.eta e := by
    intro e he
    have h0 : 0 < ∏ e ∈ G.cutEdges U, c.eta e :=
      lt_of_lt_of_le (Nat.ceil_pos.2 (by positivity)) hcard
    exact_mod_cast Nat.pos_of_ne_zero ((prod_ne_zero_iff.1 h0.ne') e he)
  -- taking logarithms, (18.41)–(18.47)
  have hlog : (n : ℝ) * τ ≤ ∑ e ∈ G.cutEdges U, (n : ℝ) * (G.cap e + δ) := by
    calc (n : ℝ) * τ = logb 2 ((2 : ℝ) ^ ((n : ℝ) * τ)) := by
          rw [Real.logb_rpow (by norm_num) (by norm_num)]
      _ ≤ logb 2 (∏ e ∈ G.cutEdges U, (c.eta e : ℝ)) :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hpow
      _ = ∑ e ∈ G.cutEdges U, logb 2 (c.eta e) :=
          Real.logb_prod _ _ fun e he => (hpos e he).ne'
      _ ≤ _ := sum_le_sum fun e _ => hη e
  rw [← mul_sum, sum_add_distrib, sum_const, nsmul_eq_mul] at hlog
  have hτ' : τ ≤ ∑ e ∈ G.cutEdges U, (G.cap e : ℝ) + (G.cutEdges U).card * δ :=
    le_of_mul_le_mul_left hlog hn0
  have hcardE : ((G.cutEdges U).card : ℝ) ≤ Fintype.card E := by
    exact_mod_cast card_le_univ _
  have hε' : ((Fintype.card E : ℝ) + 1) * δ = ε := by
    rw [hδ]
    field_simp
  nlinarith

/-- A correct code with `2^ω` messages and at most `2^{Rₑ}` tuples on every edge, for one unit of
time, makes `ω` achievable: use it `n` times. -/
theorem isAchievableInfoRate_of_code {X : Type*} [Fintype X] (c : G.TransCode s X T)
    (hc : c.Correct) {ω : ℕ} (hX : Fintype.card X = 2 ^ ω) (hη : ∀ e, c.eta e ≤ 2 ^ G.cap e) :
    G.IsAchievableInfoRate s T ω := by
  intro ε hε
  refine Eventually.of_forall fun n => ⟨ω, by linarith, ?_⟩
  have hN : ⌈(2 : ℝ) ^ ((n : ℝ) * (ω : ℝ))⌉₊ = 2 ^ (n * ω) := by
    rw [show (2 : ℝ) ^ ((n : ℝ) * (ω : ℝ)) = ((2 ^ (n * ω) : ℕ) : ℝ) by
      rw [← Nat.cast_mul, Real.rpow_natCast]; push_cast; ring]
    exact Nat.ceil_natCast _
  let φ : Fin ⌈(2 : ℝ) ^ ((n : ℝ) * (ω : ℝ))⌉₊ ≃ (Fin n → X) := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, hN, Fintype.card_fun, Fintype.card_fin, hX, ← pow_mul, mul_comm])
  refine ⟨(c.pow n).mapMsg φ, (hc.pow n).mapMsg φ, fun e => ?_⟩
  change logb 2 ((c.pow n).eta e) ≤ _
  rw [TransCode.eta_pow]
  have hle : ((c.eta e ^ n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (G.cap e * n) := by
    rw [pow_mul]
    exact_mod_cast Nat.pow_le_pow_left (hη e) n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos (c.eta e ^ n) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    positivity
  · calc logb 2 ((c.eta e ^ n : ℕ) : ℝ) ≤ logb 2 ((2 : ℝ) ^ (G.cap e * n)) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h0) hle
      _ = n * G.cap e := by
          rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
          push_cast
          ring
      _ ≤ n * (G.cap e + ε) := by nlinarith

end Bound

end PtpNetwork

end InfoTheory
