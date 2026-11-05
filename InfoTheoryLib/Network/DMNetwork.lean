/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Network.FeedbackLaw
public import InfoTheoryLib.Network.RelayBlock

/-!
# Discrete memoryless networks: codes and the cutset bound

The problem setup of Lecture 19 of El Gamal and Kim. An `N`-node discrete memoryless network is a
channel from the inputs `(x₁, …, x_N)` to the outputs `(y₁, …, y_N)`. At time `i`, node `k` sends a
function of its message and of the first `i` symbols it has received.

## Main definitions

* `restr S x`: the part `x(S)` of a tuple on the nodes of `S`.
* `DMNCode M n X Y`: codes for the network, with `M k` messages at node `k`.
* `DMNCode.law`, `DMNCode.errProb`: the joint law and the probability of error, for destination sets
  `D j ⊆ [1 : N]`.
* `IsAchievableDMN`, `dmnCapacityRegion`: achievable rates, in bits, and the capacity region.
* `cutInfo p W S`: `I(X(S); Y(Sᶜ) | X(Sᶜ))`, in nats.

## Main statements

* `DMNCode.exists_cutset_le`: the bound for each code.
* `IsAchievableDMN.exists_cutset`, `exists_cutset_of_mem_dmnCapacityRegion`: **Theorem 4 of
  Lecture 19, the cutset outer bound**.
* `IsAchievableMN.exists_cutset`, `mnCapacity_mul_log_le`: **Theorem 1 of Lecture 19**.

## Implementation notes

The notes prove the bound for one source and one cut. Here all the nodes have messages, as in
Theorem 4. For a cut `S`, the observation is the pair `(M(Sᶜ), Yⁱ(Sᶜ))`, which determines the inputs
`X(Sᶜ)` of the next time, and the law of the code is a feedback law `fbLaw`.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 19
-/

open Real Finset Filter Topology

@[expose] public noncomputable section

namespace InfoTheory

/-! ### The model -/

section Model

variable {N : ℕ} {X Y : Fin N → Type*}

/-- The part `x(S)` of a tuple on the nodes of `S`. -/
def restr {γ : Fin N → Type*} (S : Finset (Fin N)) (x : ∀ k, γ k) : ∀ k : S, γ k := fun k => x k

/-- **Page 19-38 of [elgamal2010].** An `(M, n)` code for the network: node `k` sends
`enc k i m_k (y_{k,0}, …, y_{k,i-1})` at time `i`, and estimates all the messages from its own
message and its received sequence. Only the estimates of the messages for which `k` is a
destination matter. Times are numbered from `0`. -/
structure DMNCode (M : Fin N → ℕ) (n : ℕ) (X Y : Fin N → Type*) where
  /-- The encoders. -/
  enc : ∀ k : Fin N, ∀ i : ℕ, Fin (M k) → (Fin i → Y k) → X k
  /-- The decoders. -/
  dec : ∀ k : Fin N, Fin (M k) → (Fin n → Y k) → ∀ j, Fin (M j)

variable [∀ k, Fintype (Y k)] {M : Fin N → ℕ} {n : ℕ}

/-- The encoders of all the nodes, as an encoder with feedback. -/
def DMNCode.fbEnc (c : DMNCode M n X Y) :
    ∀ i, (∀ k, Fin (M k)) → (Fin i → ∀ k, Y k) → ∀ k, X k :=
  fun i m z k => c.enc k i (m k) fun t => z t k

/-- The joint law of the messages and of the outputs, for uniform messages. -/
def DMNCode.law (c : DMNCode M n X Y) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) :
    (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ℝ :=
  fbLaw (uniformPMF (∀ k, Fin (M k))) W c.fbEnc n

/-- The event that a destination gets a message wrong. -/
def DMNCode.Wrong (c : DMNCode M n X Y) (D : Fin N → Finset (Fin N))
    (z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k)) : Prop :=
  ∃ j, ∃ k ∈ D j, c.dec k (z.1 k) (fun i => z.2 i k) j ≠ z.1 j

/-- **Page 19-38 of [elgamal2010].** The probability of error, when node `j` sends its message to
the nodes of `D j`. -/
def DMNCode.errProb (c : DMNCode M n X Y) (W : (∀ k, X k) → (∀ k, Y k) → ℝ)
    (D : Fin N → Finset (Fin N)) : ℝ :=
  ∑ z, c.law W z * ind (c.Wrong D z)

/-- **Page 19-38 of [elgamal2010].** A rate tuple, in bits, is achievable if there are codes with
`2 ^ ⌈n R_k⌉` messages at node `k` whose probability of error tends to zero. -/
def IsAchievableDMN (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (D : Fin N → Finset (Fin N))
    (R : Fin N → ℝ) : Prop :=
  ∃ c : ∀ n : ℕ, DMNCode (fun k => 2 ^ ⌈(n : ℝ) * R k⌉₊) n X Y,
    Tendsto (fun n => (c n).errProb W D) atTop (𝓝 0)

/-- **Page 19-38 of [elgamal2010].** The capacity region, in bits. -/
def dmnCapacityRegion (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (D : Fin N → Finset (Fin N)) :
    Set (Fin N → ℝ) :=
  closure {R | IsAchievableDMN W D R}

end Model

/-! ### Conditional entropies of a view of the output -/

section View

variable {α β b : Type*} [Fintype α] [Fintype β] [Fintype b]

/-- The law of the input and of a function of the output. -/
lemma dist_jointOf_view {δ : Type*} (p : α → ℝ) (W : α → β → ℝ) (v : β → δ) :
    dist (jointOf p W) (pair Prod.fst (v ∘ Prod.snd)) = jointOf p fun a => dist (W a) v := by
  classical
  funext ⟨a, d⟩
  simp only [dist, jointOf, pair, Fintype.sum_prod_type, Function.comp, Prod.mk.injEq]
  rw [sum_eq_single a]
  · simp only [true_and, mul_ite, mul_zero, mul_sum]
  · intro a' _ ha'
    exact sum_eq_zero fun y _ => ite_eq_right fun h => absurd h.1 ha'
  · simp

/-- `H(Z | B)` is concave in the law of the input, for a fixed channel to `Z` and a function `B` of
the input. -/
lemma sum_condEntropy_view_le {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : IsPMF w)
    {q : ι → α → ℝ} (hq : ∀ i, IsPMF (q i)) {K : α → β → ℝ} (hK : IsChannel K) (B : α → b) :
    ∑ i, w i * H[Prod.snd | fun z : α × β => B z.1 ; jointOf (q i) K] ≤
      H[Prod.snd | fun z : α × β => B z.1 ; jointOf (fun a => ∑ i, w i * q i a) K] := by
  classical
  have hp : IsPMF fun a => ∑ i, w i * q i a := by
    refine ⟨fun a => sum_nonneg fun i _ => mul_nonneg (hw.nonneg i) ((hq i).nonneg a), ?_⟩
    rw [sum_comm]
    simp_rw [← mul_sum, (hq _).sum_eq_one, mul_one, hw.sum_eq_one]
  let ν : ι × (α × β) → ℝ := fun z => w z.1 * jointOf (q z.1) K z.2
  have hν : IsPMF ν := by
    refine ⟨fun z => mul_nonneg (hw.nonneg _) ((jointOf_isPMF (hq _) hK).nonneg _), ?_⟩
    rw [Fintype.sum_prod_type]
    simp only [ν]
    simp_rw [← mul_sum, (jointOf_isPMF (hq _) hK).sum_eq_one, mul_one, hw.sum_eq_one]
  have hmix := condEntropy_mixture w (fun i => jointOf (q i) K)
    (fun _ => (Prod.snd : α × β → β)) (fun _ z => B z.1)
  have hle := condEntropy_le_condEntropy_comp hν (fun z => z.2.2)
    (fun z : ι × (α × β) => (z.1, B z.2.1)) Prod.snd
  have hmarg : H[fun z : ι × (α × β) => z.2.2 | Prod.snd ∘ fun z => (z.1, B z.2.1) ; ν] =
      H[Prod.snd | fun z : α × β => B z.1 ; jointOf (fun a => ∑ i, w i * q i a) K] := by
    refine condEntropy_eq_of_dist_pair_eq hν (jointOf_isPMF hp hK) ?_
    have hd : dist ν Prod.snd = jointOf (fun a => ∑ i, w i * q i a) K := by
      funext t
      simp only [dist]
      rw [Fintype.sum_prod_type]
      simp only [ν, jointOf]
      rw [sum_mul]
      refine sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single t]
      · simp [mul_assoc]
      · intro y _ h
        simp [h]
      · simp
    have h₁ : pair (Prod.snd ∘ fun z : ι × (α × β) => (z.1, B z.2.1)) (fun z => z.2.2) =
        (pair (fun z : α × β => B z.1) Prod.snd) ∘ Prod.snd := rfl
    rw [h₁, dist_comp_eq, hd]
  rw [← hmix, ← hmarg]
  exact hle

end View

/-! ### The information across a cut -/

section Cut

variable {N : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]

/-- `I(X(S); Y(Sᶜ) | X(Sᶜ))`, in nats, for the input law `p(x₁, …, x_N)`. -/
def cutInfo (p : (∀ k, X k) → ℝ) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (S : Finset (Fin N)) : ℝ :=
  I[fun z : (∀ k, X k) × (∀ k, Y k) => restr S z.1 : fun z => restr Sᶜ z.2 |
    fun z => restr Sᶜ z.1 ; jointOf p W]

/-- The channel from the inputs to the outputs `Y(Sᶜ)`. -/
def cutMarg (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (S : Finset (Fin N)) (x : ∀ k, X k) :
    (∀ k : (Sᶜ : Finset (Fin N)), Y k) → ℝ :=
  dist (W x) (restr Sᶜ)

variable {p : (∀ k, X k) → ℝ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

omit [∀ k, Fintype (X k)] in
lemma cutMarg_isChannel (hW : IsChannel W) (S : Finset (Fin N)) : IsChannel (cutMarg W S) :=
  fun x => (hW x).dist _

lemma restr_compl_restr_injective {γ : Fin N → Type*} (S : Finset (Fin N)) :
    Function.Injective fun x : ∀ k, γ k => (restr Sᶜ x, restr S x) := by
  intro x x' h
  funext k
  by_cases hk : k ∈ S
  · exact congrFun (Prod.ext_iff.mp h).2 ⟨k, hk⟩
  · exact congrFun (Prod.ext_iff.mp h).1 ⟨k, by simpa using hk⟩

/-- `I(X(S); Y(Sᶜ) | X(Sᶜ)) = H(Y(Sᶜ) | X(Sᶜ)) - H(Y(Sᶜ) | X₁, …, X_N)`. -/
lemma cutInfo_eq (hp : IsPMF p) (hW : IsChannel W) (S : Finset (Fin N)) :
    cutInfo p W S = H[Prod.snd | fun z : (∀ k, X k) × _ => restr Sᶜ z.1 ;
        jointOf p (cutMarg W S)] - ∑ x, p x * entropy (cutMarg W S x) := by
  classical
  have hμ := jointOf_isPMF hp hW
  have hK := cutMarg_isChannel hW S
  have hν := jointOf_isPMF hp hK
  have hview := dist_jointOf_view p W (restr Sᶜ)
  rw [cutInfo, condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
  congr 1
  · refine condEntropy_eq_of_dist_pair_eq hμ hν ?_
    have e : pair (fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.1) (fun z => restr Sᶜ z.2) =
        (fun t : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) => (restr Sᶜ t.1, t.2)) ∘
          pair Prod.fst (restr Sᶜ ∘ Prod.snd) := rfl
    have e' : pair (fun z : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) => restr Sᶜ z.1)
        Prod.snd = fun t : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) =>
          (restr Sᶜ t.1, t.2) := rfl
    rw [e, dist_comp_eq, hview, e']
    rfl
  · have h₁ : H[fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.2 | pair (fun z => restr Sᶜ z.1)
        (fun z => restr S z.1) ; jointOf p W] =
        H[fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.2 | Prod.fst ; jointOf p W] :=
      condEntropy_congr_right hμ _ (fun x : ∀ k, X k => (restr Sᶜ x, restr S x))
        (restr_compl_restr_injective S) fun _ => rfl
    rw [h₁]
    have hchan : ∀ (x : ∀ k, X k) (d : ∀ k : (Sᶜ : Finset (Fin N)), Y k),
        dist (jointOf p W) (pair Prod.fst fun z => restr Sᶜ z.2) (x, d) =
          dist (jointOf p W) Prod.fst x * cutMarg W S (id x) d := by
      intro x d
      have := congrFun hview (x, d)
      rw [dist_jointOf_fst hW]
      exact this
    have h₂ := condEntropy_of_channel (f := id) hchan
    rw [h₂]
    refine sum_congr rfl fun x _ => ?_
    have e : (id ∘ Prod.fst : (∀ k, X k) × (∀ k, Y k) → ∀ k, X k) = Prod.fst := rfl
    rw [e, dist_jointOf_fst hW]

/-- **Page 19-7 of [elgamal2010].** `I(X(S); Y(Sᶜ) | X(Sᶜ))` is concave in the input law: this
replaces the time sharing variable of the notes. -/
lemma sum_cutInfo_le {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw : IsPMF w)
    {q : ι → (∀ k, X k) → ℝ} (hq : ∀ i, IsPMF (q i)) (hW : IsChannel W) (S : Finset (Fin N)) :
    ∑ i, w i * cutInfo (q i) W S ≤ cutInfo (fun a => ∑ i, w i * q i a) W S := by
  classical
  have hp : IsPMF fun a => ∑ i, w i * q i a := by
    refine ⟨fun a => sum_nonneg fun i _ => mul_nonneg (hw.nonneg i) ((hq i).nonneg a), ?_⟩
    rw [sum_comm]
    simp_rw [← mul_sum, (hq _).sum_eq_one, mul_one, hw.sum_eq_one]
  simp_rw [cutInfo_eq (hq _) hW]
  rw [cutInfo_eq hp hW]
  simp_rw [mul_sub, sum_sub_distrib]
  have hlin : ∑ a, (∑ i, w i * q i a) * entropy (cutMarg W S a) =
      ∑ i, w i * ∑ a, q i a * entropy (cutMarg W S a) := by
    simp_rw [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun a _ => mul_assoc _ _ _
  rw [hlin]
  have := sum_condEntropy_view_le hw hq (cutMarg_isChannel hW S) (restr Sᶜ)
  linarith

/-- The information across a cut is at most the logarithm of the number of outputs. -/
lemma cutInfo_le_log_card (hp : IsPMF p) (hW : IsChannel W) (S : Finset (Fin N)) :
    cutInfo p W S ≤ log (Fintype.card (∀ k : (Sᶜ : Finset (Fin N)), Y k)) := by
  have hK := cutMarg_isChannel hW S
  have hν := jointOf_isPMF hp hK
  rw [cutInfo_eq hp hW]
  have h₁ := condEntropy_le_entropy hν Prod.snd
    (fun z : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) => restr Sᶜ z.1)
  have h₂ := entropyRV_le_log_card hν
    (Prod.snd : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) → _)
  have h₃ : 0 ≤ ∑ x, p x * entropy (cutMarg W S x) :=
    sum_nonneg fun x _ => mul_nonneg (hp.nonneg x) (entropy_nonneg (hK x))
  linarith

/-- The information across a cut is nonnegative. -/
lemma cutInfo_nonneg (hp : IsPMF p) (hW : IsChannel W) (S : Finset (Fin N)) :
    0 ≤ cutInfo p W S :=
  condMutualInfo_nonneg (jointOf_isPMF hp hW) _ _ _

/-- The entropies are continuous in the input law. -/
lemma continuous_entropyRV_jointOf_input {α β a : Type*} [Fintype α] [Fintype β] [Fintype a]
    (W : α → β → ℝ) (A : α × β → a) :
    Continuous fun p : α → ℝ => H[A ; jointOf p W] := by
  classical
  simp only [entropyRV, entropy_eq_sum_negMulLog]
  refine continuous_finsetSum _ fun v _ => continuous_negMulLog.comp ?_
  simp only [dist]
  refine continuous_finsetSum _ fun z _ => ?_
  split_ifs
  · simp only [jointOf]
    fun_prop
  · exact continuous_const

/-- The information across a cut is continuous in the input law. -/
lemma continuous_cutInfo (hW : IsChannel W) (S : Finset (Fin N)) :
    ContinuousOn (fun p : (∀ k, X k) → ℝ => cutInfo p W S) {p | IsPMF p} := by
  classical
  have heq : ∀ p : (∀ k, X k) → ℝ, IsPMF p → cutInfo p W S =
      H[pair (fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.1) (fun z => restr S z.1) ; jointOf p W]
        - H[fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.1 ; jointOf p W]
        - (H[pair (pair (fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.2) (fun z => restr Sᶜ z.1))
            (fun z => restr S z.1) ; jointOf p W]
          - H[pair (fun z : (∀ k, X k) × (∀ k, Y k) => restr Sᶜ z.2) (fun z => restr Sᶜ z.1) ;
              jointOf p W]) := by
    intro p hp
    have hμ := jointOf_isPMF hp hW
    rw [cutInfo, condMutualInfo, condEntropy_eq_sub hμ, condEntropy_eq_sub hμ]
  refine ContinuousOn.congr (Continuous.continuousOn ?_) fun p hp => heq p hp
  exact ((continuous_entropyRV_jointOf_input W _).sub
    (continuous_entropyRV_jointOf_input W _)).sub
    ((continuous_entropyRV_jointOf_input W _).sub (continuous_entropyRV_jointOf_input W _))

end Cut

/-! ### One use of the channel -/

section Step

variable {N n : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  {M : Fin N → ℕ} {W : (∀ k, X k) → (∀ k, Y k) → ℝ}

/-- The law of the inputs at time `i`. -/
def DMNCode.letter (c : DMNCode M n X Y) (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (i : Fin n) :
    (∀ k, X k) → ℝ :=
  dist (c.law W) fun z => c.fbEnc i z.1 (fbPre i z.2)

omit [∀ k, Fintype (X k)] in
lemma DMNCode.law_isPMF (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k) (hW : IsChannel W) :
    IsPMF (c.law W) := by
  have : Nonempty (∀ k, Fin (M k)) := ⟨fun k => ⟨0, hM k⟩⟩
  exact fbLaw_isPMF uniformPMF_isPMF hW n

lemma DMNCode.letter_isPMF (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k) (hW : IsChannel W)
    (i : Fin n) : IsPMF (c.letter W i) :=
  (c.law_isPMF hM hW).dist _

/-- The observation of the side `Sᶜ` of the cut after `i` uses of the channel: the pair
`(M(Sᶜ), Yⁱ(Sᶜ))`. -/
def cutObs (S : Finset (Fin N)) (i : ℕ) (hi : i ≤ n)
    (z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k)) :
    (∀ k : (Sᶜ : Finset (Fin N)), Fin (M k)) × (Fin i → ∀ k : (Sᶜ : Finset (Fin N)), Y k) :=
  (restr Sᶜ z.1, fun t => restr Sᶜ (z.2 (Fin.castLE hi t)))

/-- **Page 19-6 of [elgamal2010].**
`I(M(S); M(Sᶜ), Yⁱ⁺¹(Sᶜ)) ≤ I(M(S); M(Sᶜ), Yⁱ(Sᶜ)) + I(Xᵢ(S); Yᵢ(Sᶜ) | Xᵢ(Sᶜ))`. -/
theorem DMNCode.mutualInfo_cutObs_succ_le (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k)
    (hW : IsChannel W) (S : Finset (Fin N)) (i : ℕ) (hi : i < n) :
    I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : cutObs S (i + 1) hi ; c.law W]
      ≤ I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : cutObs S i hi.le ; c.law W]
        + cutInfo (c.letter W ⟨i, hi⟩) W S := by
  classical
  have : Nonempty (∀ k, Fin (M k)) := ⟨fun k => ⟨0, hM k⟩⟩
  set μ := c.law W with hμdef
  have hμ : IsPMF μ := c.law_isPMF hM hW
  have hp := c.letter_isPMF hM hW ⟨i, hi⟩
  let i' : Fin n := ⟨i, hi⟩
  let A : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ∀ k : S, Fin (M k) := fun z => restr S z.1
  let Yl : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ∀ k : (Sᶜ : Finset (Fin N)), Y k :=
    fun z => restr Sᶜ (z.2 i')
  let O := cutObs (M := M) (Y := Y) (n := n) S i hi.le
  have h1 : I[A : cutObs S (i + 1) hi ; μ] = I[A : pair Yl O ; μ] := by
    refine mutualInfo_congr_right hμ A
      (fun v : (∀ k : (Sᶜ : Finset (Fin N)), Y k) × _ => (v.2.1, (Fin.snoc v.2.2 v.1 :
        Fin (i + 1) → ∀ k : (Sᶜ : Finset (Fin N)), Y k))) (fun a b hab => ?_) fun z => ?_
    · simp only [Prod.mk.injEq] at hab
      have := snoc_injective2 (α := ∀ k : (Sᶜ : Finset (Fin N)), Y k) i
        (a₁ := (a.2.2, a.1)) (a₂ := (b.2.2, b.1)) hab.2
      simp only [Prod.mk.injEq] at this
      exact Prod.ext this.2 (Prod.ext hab.1 this.1)
    · refine Prod.ext rfl ?_
      funext t
      refine Fin.lastCases ?_ (fun j => ?_) t
      · simp only [cutObs, pair, Fin.snoc_last, Yl]
        rfl
      · simp only [cutObs, pair, O, Fin.snoc_castSucc]
        rfl
  have h2 := chain_rule_mutualInfo₂ hμ A Yl O
  have h4 : I[A : Yl | O ; μ] = H[Yl | O ; μ] - H[Yl | pair O A ; μ] := by
    rw [condMutualInfo_comm hμ, condMutualInfo_eq' hμ]
  -- the inputs of the side `Sᶜ` are a function of the observation
  let Xin : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ∀ k, X k :=
    fun z => c.fbEnc i' z.1 (fbPre i' z.2)
  let Xc : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ∀ k : (Sᶜ : Finset (Fin N)), X k :=
    fun z => restr Sᶜ (Xin z)
  have h5 : H[Yl | O ; μ] ≤ H[Yl | Xc ; μ] :=
    condEntropy_le_condEntropy_comp hμ Yl O
      fun u (k : (Sᶜ : Finset (Fin N))) => c.enc k i (u.1 k) fun t => u.2 t k
  -- the conditional entropy given everything
  let G : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → (∀ k, Fin (M k)) × (Fin i' → ∀ k, Y k) :=
    fun z => (z.1, fbPre i' z.2)
  have h6 : H[Yl | G ; μ] ≤ H[Yl | pair O A ; μ] :=
    condEntropy_le_condEntropy_comp hμ Yl G fun u =>
      ((restr Sᶜ u.1, fun t => restr Sᶜ (u.2 t)), restr S u.1)
  have hchanG : ∀ (z : (∀ k, Fin (M k)) × (Fin i' → ∀ k, Y k))
      (d : ∀ k : (Sᶜ : Finset (Fin N)), Y k), dist μ (pair G Yl) (z, d) =
        dist μ G z * cutMarg W S (c.fbEnc i' z.1 z.2) d := fun z d =>
    dist_fbLaw_letter_view hW i' (fun t => t) (fun t => c.fbEnc i' t.1 t.2) (fun _ _ => rfl)
      (restr Sᶜ) z d
  have h7 := condEntropy_of_channel (f := fun z : (∀ k, Fin (M k)) × (Fin i' → ∀ k, Y k) =>
    c.fbEnc i' z.1 z.2) hchanG
  have h8 : ∑ x, dist μ ((fun z : (∀ k, Fin (M k)) × (Fin i' → ∀ k, Y k) =>
      c.fbEnc i' z.1 z.2) ∘ G) x * entropy (cutMarg W S x) =
        ∑ x, c.letter W i' x * entropy (cutMarg W S x) := rfl
  -- the conditional entropy given the inputs of the side `Sᶜ`
  have hchanX : ∀ (x : ∀ k, X k) (d : ∀ k : (Sᶜ : Finset (Fin N)), Y k),
      dist μ (pair Xin Yl) (x, d) = dist μ Xin x * cutMarg W S x d := fun x d =>
    dist_fbLaw_letter_view hW i' (fun t => c.fbEnc i' t.1 t.2) id (fun _ _ => rfl) (restr Sᶜ) x d
  have hK := cutMarg_isChannel (X := X) hW S
  have h9 : H[Yl | Xc ; μ] = H[Prod.snd | fun z : (∀ k, X k) × _ => restr Sᶜ z.1 ;
      jointOf (c.letter W i') (cutMarg W S)] := by
    refine condEntropy_eq_of_dist_pair_eq hμ (jointOf_isPMF hp hK) ?_
    have hd : dist μ (pair Xin Yl) = jointOf (c.letter W i') (cutMarg W S) := by
      funext ⟨x, d⟩
      exact hchanX x d
    have e : pair Xc Yl = (fun t : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) =>
        (restr Sᶜ t.1, t.2)) ∘ pair Xin Yl := rfl
    have e' : pair (fun z : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) => restr Sᶜ z.1)
        Prod.snd = fun t : (∀ k, X k) × (∀ k : (Sᶜ : Finset (Fin N)), Y k) =>
          (restr Sᶜ t.1, t.2) := rfl
    rw [e, dist_comp_eq, hd, e']
  have h10 := cutInfo_eq hp hW S
  have h11 : I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : cutObs S (i + 1) hi ;
      μ] = I[A : cutObs S (i + 1) hi ; μ] := rfl
  rw [h11, h1, h2]
  have h12 : I[A : O ; μ] = I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 :
      cutObs S i hi.le ; μ] := rfl
  rw [← h12]
  linarith

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] in
/-- The number of messages of a set of nodes. -/
lemma log_card_restr (hM : ∀ k, 0 < M k) (S : Finset (Fin N)) :
    log (Fintype.card (∀ k : S, Fin (M k))) = ∑ k ∈ S, log (M k) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Finset.prod_coe_sort S fun k => M k, Nat.cast_prod, log_prod]
  exact fun k _ => by exact_mod_cast (hM k).ne'

omit [∀ k, Fintype (X k)] in
/-- The entropy of the messages. -/
lemma DMNCode.entropy_fst_law (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k) (hW : IsChannel W) :
    H[Prod.fst ; c.law W] = ∑ k, log (M k) := by
  have : Nonempty (∀ k, Fin (M k)) := ⟨fun k => ⟨0, hM k⟩⟩
  have hd : dist (c.law W) Prod.fst = uniformPMF (∀ k, Fin (M k)) := dist_fst_fbLaw hW n
  rw [entropyRV, hd, entropy_uniformPMF, Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Nat.cast_prod, log_prod]
  exact fun k _ => by exact_mod_cast (hM k).ne'

omit [∀ k, Fintype (X k)] in
/-- The messages of the two sides of a cut are independent. -/
lemma DMNCode.mutualInfo_cutObs_zero_le (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k)
    (hW : IsChannel W) (S : Finset (Fin N)) :
    I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 :
      cutObs S 0 (Nat.zero_le n) ; c.law W] ≤ 0 := by
  classical
  have hμ : IsPMF (c.law W) := c.law_isPMF hM hW
  have hH := c.entropy_fst_law hM hW
  set μ := c.law W
  let A : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ∀ k : S, Fin (M k) := fun z => restr S z.1
  let O := cutObs (M := M) (Y := Y) (n := n) S 0 (Nat.zero_le n)
  have hI := mutualInfo_eq_add_sub hμ A O
  have hA := entropyRV_le_log_card hμ A
  have hO : H[O ; μ] ≤ log (Fintype.card (∀ k : (Sᶜ : Finset (Fin N)), Fin (M k))) := by
    have e : H[O ; μ] = H[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr Sᶜ z.1 ; μ] := by
      refine entropyRV_eq_of_injective μ (fun m => (m, fun t => t.elim0))
        (fun a b hab => (Prod.ext_iff.mp hab).1) fun z => Prod.ext rfl (funext fun t => t.elim0)
    rw [e]
    exact entropyRV_le_log_card hμ _
  have hP : H[pair A O ; μ] = H[Prod.fst ; μ] := by
    refine entropyRV_eq_of_injective μ
      (fun m : ∀ k, Fin (M k) => (restr S m, (restr Sᶜ m, fun t => t.elim0))) (fun a b hab => ?_)
      fun z => Prod.ext rfl (Prod.ext rfl (funext fun t => t.elim0))
    simp only [Prod.mk.injEq] at hab
    exact restr_compl_restr_injective S (Prod.ext hab.2.1 hab.1)
  rw [log_card_restr hM] at hA hO
  have hsum := sum_add_sum_compl S fun k => log (M k : ℝ)
  have h₁ : I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 :
      cutObs S 0 (Nat.zero_le n) ; μ] = I[A : O ; μ] := rfl
  rw [h₁, hI, hP, hH]
  linarith

/-- The sum of the informations over the uses of the channel. -/
lemma DMNCode.mutualInfo_cutObs_le_sum (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k)
    (hW : IsChannel W) (S : Finset (Fin N)) : ∀ (i : ℕ) (hi : i ≤ n),
    I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : cutObs S i hi ; c.law W] ≤
      ∑ t : Fin i, cutInfo (c.letter W (Fin.castLE hi t)) W S
  | 0, hi => by simpa using c.mutualInfo_cutObs_zero_le hM hW S
  | i + 1, hi => by
    rw [Fin.sum_univ_castSucc]
    have h₁ := c.mutualInfo_cutObs_succ_le hM hW S i hi
    have h₂ := c.mutualInfo_cutObs_le_sum hM hW S i ((Nat.lt_succ_self i).le.trans hi)
    exact h₁.trans (add_le_add h₂ le_rfl)

/-- The source nodes of the messages that have to cross the cut `S`. -/
def crossing (D : Fin N → Finset (Fin N)) (S : Finset (Fin N)) : Finset (Fin N) :=
  S.filter fun j => (D j ∩ Sᶜ).Nonempty

omit [∀ k, Fintype (X k)] in
/-- **Fano's inequality for a cut.** The side `Sᶜ` decodes the messages that cross the cut. -/
lemma DMNCode.one_sub_errProb_mul_le (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k)
    (hW : IsChannel W) (D : Fin N → Finset (Fin N)) (S : Finset (Fin N)) :
    (1 - c.errProb W D) * ∑ k ∈ crossing D S, log (M k) ≤ log 2 +
      I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : cutObs S n le_rfl ;
        c.law W] := by
  classical
  have hμ : IsPMF (c.law W) := c.law_isPMF hM hW
  have hH := c.entropy_fst_law hM hW
  set μ := c.law W with hμd
  set T := crossing D S with hT
  have hTS : T ⊆ S := filter_subset _ _
  let O := cutObs (M := M) (Y := Y) (n := n) S n le_rfl
  let A : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ∀ k : T, Fin (M k) := fun z => restr T z.1
  -- the destination that decodes a message
  have hdest : ∀ j : T, ∃ k, k ∈ D j ∧ k ∈ (Sᶜ : Finset (Fin N)) := fun j => by
    obtain ⟨k, hk⟩ := (mem_filter.mp j.2).2
    exact ⟨k, (mem_inter.mp hk).1, (mem_inter.mp hk).2⟩
  choose dk hdk hdc using hdest
  let g : ((∀ k : (Sᶜ : Finset (Fin N)), Fin (M k)) ×
      (Fin n → ∀ k : (Sᶜ : Finset (Fin N)), Y k)) → ∀ k : T, Fin (M k) := fun o j =>
    c.dec (dk j) (o.1 ⟨dk j, hdc j⟩) (fun i => o.2 i ⟨dk j, hdc j⟩) j
  have hF := fano_weak hμ A O g
  have hP : InfoTheory.errProb μ A O g ≤ c.errProb W D := by
    simp only [InfoTheory.errProb, DMNCode.errProb]
    refine sum_le_sum fun z _ => ?_
    by_cases h : g (O z) = A z
    · rw [ite_eq_right (fun h' => absurd h h')]
      exact mul_nonneg (hμ.nonneg z) (ind_nonneg _)
    · rw [ite_eq_left h, ind_of_pos, mul_one]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp h
      exact ⟨j, dk j, hdk j, hj⟩
  have hL := log_card_restr (M := M) hM T
  have hP0 : 0 ≤ InfoTheory.errProb μ A O g := errProb_nonneg hμ _ _ _
  have hL0 : 0 ≤ log (Fintype.card (∀ k : T, Fin (M k))) := by
    rw [hL]
    exact sum_nonneg fun k _ => log_natCast_nonneg _
  -- the messages that cross the cut have full entropy
  let B : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) → ∀ k : (Tᶜ : Finset (Fin N)), Fin (M k) :=
    fun z => restr Tᶜ z.1
  have hAB : H[Prod.fst ; μ] = H[pair B A ; μ] :=
    (entropyRV_eq_of_injective μ (fun x : ∀ k, Fin (M k) => (restr Tᶜ x, restr T x))
      (restr_compl_restr_injective T) fun _ => rfl).symm
  have hsub := mutualInfo_eq_add_sub hμ B A
  have hnn := mutualInfo_nonneg hμ B A
  have hB := entropyRV_le_log_card hμ B
  rw [log_card_restr hM] at hB
  have hsum := sum_add_sum_compl T fun k => log (M k : ℝ)
  have hHA : ∑ k ∈ T, log (M k : ℝ) ≤ H[A ; μ] := by linarith
  have hI := mutualInfo_eq_entropy_sub_condEntropy hμ A O
  -- data processing
  have hdp : I[A : O ; μ] ≤
    I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : O ; μ] := by
    rw [mutualInfo_comm hμ A O, mutualInfo_comm hμ _ O]
    exact mutualInfo_comp_le hμ O (fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1)
      fun t (k : T) => t ⟨k, hTS k.2⟩
  have hE : c.errProb W D * ∑ k ∈ T, log (M k : ℝ) ≥
      InfoTheory.errProb μ A O g * ∑ k ∈ T, log (M k : ℝ) :=
    mul_le_mul_of_nonneg_right hP (hL ▸ hL0)
  rw [hL] at hF
  have h₁ : I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : cutObs S n le_rfl ;
      μ] = I[fun z : (∀ k, Fin (M k)) × (Fin n → ∀ k, Y k) => restr S z.1 : O ; μ] := rfl
  rw [h₁]
  linarith

/-- **Pages 19-6 and 19-7 of [elgamal2010].** For every code there is an input law such that, for
all the cuts, `(1 - P_e) ∑_{k ∈ S : D_k ∩ Sᶜ ≠ ∅} log M_k ≤ log 2 + n I(X(S); Y(Sᶜ) | X(Sᶜ))`. -/
theorem DMNCode.exists_cutset_le (c : DMNCode M n X Y) (hM : ∀ k, 0 < M k) (hn : 0 < n)
    (hW : IsChannel W) (D : Fin N → Finset (Fin N)) :
    ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ S, (1 - c.errProb W D) * ∑ k ∈ crossing D S, log (M k) ≤
      log 2 + n * cutInfo p W S := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hq : ∀ i : Fin n, IsPMF (c.letter W i) := c.letter_isPMF hM hW
  let w : Fin n → ℝ := uniformPMF (Fin n)
  have hw : IsPMF w := uniformPMF_isPMF
  have hwv : ∀ i, w i = 1 / n := fun i => by simp [w, uniformPMF]
  let p : (∀ k, X k) → ℝ := fun a => ∑ i : Fin n, w i * c.letter W i a
  have hp : IsPMF p := by
    refine ⟨fun a => sum_nonneg fun i _ => mul_nonneg (hw.nonneg i) ((hq i).nonneg a), ?_⟩
    simp only [p]
    rw [sum_comm]
    simp_rw [← mul_sum, (hq _).sum_eq_one, mul_one, hw.sum_eq_one]
  refine ⟨p, hp, fun S => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h₁ := c.one_sub_errProb_mul_le hM hW D S
  have h₂ := c.mutualInfo_cutObs_le_sum hM hW S n le_rfl
  have h₃ := sum_cutInfo_le hw hq hW S
  have h₄ : ∑ t : Fin n, cutInfo (c.letter W (Fin.castLE le_rfl t)) W S =
      n * ∑ t : Fin n, w t * cutInfo (c.letter W t) W S := by
    rw [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [hwv]
    have : Fin.castLE le_rfl t = t := rfl
    rw [this]
    field_simp
  have h₅ := mul_le_mul_of_nonneg_left h₃ hn'.le
  linarith

end Step

/-! ### The cutset outer bound -/

section Outer

variable {N : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {D : Fin N → Finset (Fin N)} {R : Fin N → ℝ}

/-- **Theorem 4 of Lecture 19 of [elgamal2010], page 19-39: the cutset outer bound.** If a rate
tuple is achievable, then for some `p(x₁, …, x_N)` and all the cuts `S`,
`∑_{k ∈ S : D_k ∩ Sᶜ ≠ ∅} R_k ≤ I(X(S); Y(Sᶜ) | X(Sᶜ))`, where the rates are converted to nats. -/
theorem IsAchievableDMN.exists_cutset (hW : IsChannel W) (h : IsAchievableDMN W D R) :
    ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧
      ∀ S, (∑ k ∈ crossing D S, R k) * log 2 ≤ cutInfo p W S := by
  classical
  obtain ⟨c, hc⟩ := h
  have hpos : ∀ (n : ℕ) (k : Fin N), 0 < 2 ^ ⌈(n : ℝ) * R k⌉₊ := fun n k => by positivity
  have hex := fun n : ℕ => (c (n + 1)).exists_cutset_le (hpos (n + 1)) (Nat.succ_pos n) hW D
  choose p hp hle using hex
  obtain ⟨q, hq, φ, hφ, hlim⟩ := isCompact_setOf_isPMF.tendsto_subseq hp
  refine ⟨q, hq, fun S => ?_⟩
  -- the bound along the subsequence
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  set r := (∑ k ∈ crossing D S, R k) * log 2 with hr
  have hP1 : ∀ n, (c n).errProb W D ≤ 1 := fun n => by
    have hμ := (c n).law_isPMF (hpos n) hW
    calc (c n).errProb W D ≤ ∑ z, (c n).law W z * 1 :=
          sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (ind_le_one _) (hμ.nonneg z)
      _ = 1 := by simp [hμ.sum_eq_one]
  have hbound : ∀ n : ℕ, (1 - (c (n + 1)).errProb W D) * r ≤
      log 2 / ((n + 1 : ℕ) : ℝ) + cutInfo (p n) W S := by
    intro n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h₁ := hle n S
    have h₂ : ((n + 1 : ℕ) : ℝ) * r ≤ ∑ k ∈ crossing D S,
        log ((2 ^ ⌈((n + 1 : ℕ) : ℝ) * R k⌉₊ : ℕ) : ℝ) := by
      rw [hr, ← mul_assoc, mul_sum, sum_mul]
      refine sum_le_sum fun k _ => ?_
      push_cast
      rw [log_pow]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_ceil _) hlog.le
    have h₃ := mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr (hP1 (n + 1)))
    have h₄ : ((n + 1 : ℕ) : ℝ) * (log 2 / ((n + 1 : ℕ) : ℝ) + cutInfo (p n) W S) =
        log 2 + ((n + 1 : ℕ) : ℝ) * cutInfo (p n) W S := by
      field_simp
    have h₅ : ((n + 1 : ℕ) : ℝ) * ((1 - (c (n + 1)).errProb W D) * r) ≤
        ((n + 1 : ℕ) : ℝ) * (log 2 / ((n + 1 : ℕ) : ℝ) + cutInfo (p n) W S) := by
      rw [h₄]
      calc _ = (1 - (c (n + 1)).errProb W D) * (((n + 1 : ℕ) : ℝ) * r) := by ring
        _ ≤ _ := h₃.trans h₁
    exact le_of_mul_le_mul_left h₅ hn
  have hL : Tendsto (fun n => (1 - (c (φ n + 1)).errProb W D) * r) atTop (𝓝 ((1 - 0) * r)) := by
    refine ((tendsto_const_nhds.sub ?_).mul_const r)
    exact hc.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
  have hR : Tendsto (fun n => log 2 / ((φ n + 1 : ℕ) : ℝ) + cutInfo (p (φ n)) W S) atTop
      (𝓝 (0 + cutInfo q W S)) := by
    refine Tendsto.add ?_ ?_
    · refine Tendsto.div_atTop tendsto_const_nhds ?_
      exact tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
    · have hcont := (continuous_cutInfo hW S) q hq
      exact hcont.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hp _⟩)
  have := le_of_tendsto_of_tendsto' hL hR fun n => hbound (φ n)
  simpa using this

/-- **Theorem 4 of Lecture 19 of [elgamal2010], page 19-39**, for the capacity region. -/
theorem exists_cutset_of_mem_dmnCapacityRegion (hW : IsChannel W)
    (h : R ∈ dmnCapacityRegion W D) :
    ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧
      ∀ S, (∑ k ∈ crossing D S, R k) * log 2 ≤ cutInfo p W S := by
  classical
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp h
  have hex := fun n => IsAchievableDMN.exists_cutset hW (hu n)
  choose p hp hle using hex
  obtain ⟨q, hq, φ, hφ, hplim⟩ := isCompact_setOf_isPMF.tendsto_subseq hp
  refine ⟨q, hq, fun S => ?_⟩
  have hL : Tendsto (fun n => (∑ k ∈ crossing D S, u (φ n) k) * log 2) atTop
      (𝓝 ((∑ k ∈ crossing D S, R k) * log 2)) := by
    refine Tendsto.mul_const _ (tendsto_finsetSum _ fun k _ => ?_)
    exact (tendsto_pi_nhds.mp hlim k).comp hφ.tendsto_atTop
  have hR : Tendsto (fun n => cutInfo (p (φ n)) W S) atTop (𝓝 (cutInfo q W S)) :=
    ((continuous_cutInfo hW S) q hq).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hplim, Eventually.of_forall fun n => hp _⟩)
  exact le_of_tendsto_of_tendsto' hL hR fun n => hle (φ n) S

end Outer

/-! ### Multicast networks -/

section Multicast

variable {N : ℕ} {X Y : Fin N → Type*} [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)]
  {W : (∀ k, X k) → (∀ k, Y k) → ℝ} {s : Fin N} {D : Finset (Fin N)} {R : ℝ}

/-- The destinations of a multicast network: only the source `s` has a message. -/
def mcDest (s : Fin N) (D : Finset (Fin N)) : Fin N → Finset (Fin N) :=
  fun j => if j = s then D else ∅

/-- The rates of a multicast network. -/
def mcRate (s : Fin N) (R : ℝ) : Fin N → ℝ := fun j => if j = s then R else 0

/-- **Page 19-3 of [elgamal2010].** A rate is achievable for the discrete memoryless multicast
network with source `s` and destinations `D`. The other nodes have a rate `0`, that is one message.
The notes take `s = 1` and `Y₁ = ∅`; when `Y s` is not trivial the source also has feedback. -/
def IsAchievableMN (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (s : Fin N) (D : Finset (Fin N)) (R : ℝ) :
    Prop :=
  IsAchievableDMN W (mcDest s D) (mcRate s R)

/-- **Page 19-3 of [elgamal2010].** The capacity of the multicast network, in bits. -/
def mnCapacity (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (s : Fin N) (D : Finset (Fin N)) : ℝ :=
  sSup {R | IsAchievableMN W s D R}

/-- **Theorem 1 of Lecture 19 of [elgamal2010], page 19-5.** The cutset bound
`max_{p(xᴺ)} min_{k ∈ D} min_{S : s ∈ S, k ∈ Sᶜ} I(X(S); Y(Sᶜ) | X(Sᶜ))`, in nats. -/
def mnCutsetBound (W : (∀ k, X k) → (∀ k, Y k) → ℝ) (s : Fin N) (D : Finset (Fin N)) : ℝ :=
  sSup {v | ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S → k ∉ S →
    v ≤ cutInfo p W S}

omit [∀ k, Fintype (X k)] [∀ k, Fintype (Y k)] in
lemma sum_crossing_mcRate {S : Finset (Fin N)} (hs : s ∈ S) {k : Fin N} (hk : k ∈ D) (hkS : k ∉ S) :
    ∑ j ∈ crossing (mcDest s D) S, mcRate s R j = R := by
  rw [sum_eq_single s]
  · simp [mcRate]
  · intro j _ hj
    simp [mcRate, hj]
  · intro h
    refine absurd ?_ h
    refine mem_filter.mpr ⟨hs, k, ?_⟩
    simp only [mcDest, ite_true, mem_inter, mem_compl]
    exact ⟨hk, hkS⟩

/-- **Theorem 1 of Lecture 19 of [elgamal2010], page 19-5: the cutset bound.** If `R` is achievable,
then there is an input law for which `R` is at most the information across every cut that separates
the source from a destination. -/
theorem IsAchievableMN.exists_cutset (hW : IsChannel W) (h : IsAchievableMN W s D R) :
    ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S → k ∉ S →
      R * log 2 ≤ cutInfo p W S := by
  obtain ⟨p, hp, hle⟩ := IsAchievableDMN.exists_cutset hW h
  refine ⟨p, hp, fun k hk S hs hkS => ?_⟩
  have := hle S
  rwa [sum_crossing_mcRate hs hk hkS] at this

/-- The values of the cutset bound are bounded, if the source has another destination. -/
lemma bddAbove_mnCutset (hW : IsChannel W) {k : Fin N} (hk : k ∈ D) (hsk : s ≠ k) :
    BddAbove {v | ∃ p : (∀ k, X k) → ℝ, IsPMF p ∧ ∀ k ∈ D, ∀ S : Finset (Fin N), s ∈ S → k ∉ S →
      v ≤ cutInfo p W S} := by
  refine ⟨log (Fintype.card (∀ j : (({s} : Finset (Fin N))ᶜ : Finset (Fin N)), Y j)), ?_⟩
  rintro v ⟨p, hp, h⟩
  exact (h k hk {s} (mem_singleton_self s) (by simpa using hsk.symm)).trans
    (cutInfo_le_log_card hp hW _)

/-- **Theorem 1 of Lecture 19 of [elgamal2010], page 19-5.** The capacity, converted to nats, is at
most the cutset bound. -/
theorem mnCapacity_mul_log_le [∀ k, Nonempty (X k)] (hW : IsChannel W) {k : Fin N} (hk : k ∈ D)
    (hsk : s ≠ k) : mnCapacity W s D * log 2 ≤ mnCutsetBound W s D := by
  have hlog : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hbd := bddAbove_mnCutset (s := s) hW hk hsk
  have h0 : 0 ≤ mnCutsetBound W s D := by
    refine le_csSup hbd ⟨uniformPMF _, uniformPMF_isPMF, fun _ _ S _ _ => ?_⟩
    exact cutInfo_nonneg uniformPMF_isPMF hW S
  rw [← le_div_iff₀ hlog]
  refine Real.sSup_le (fun R hR => ?_) (div_nonneg h0 hlog.le)
  rw [le_div_iff₀ hlog]
  obtain ⟨p, hp, hle⟩ := IsAchievableMN.exists_cutset hW hR
  exact le_csSup hbd ⟨p, hp, hle⟩

end Multicast

end InfoTheory
