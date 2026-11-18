/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.ChannelCoding.Converse
public import InfoTheoryLib.Network.JSCCMACLaw

/-!
# Shannon's secrecy system

Theorem 1 of Lecture 23 of El Gamal and Kim. A sender and a receiver share a key `K`, and an
eavesdropper observes the ciphertext `L`. The system has perfect secrecy if the receiver recovers
the message `M` from `(L, K)` and `I(M; L) = 0`.

## Main statements

* `entropy_le_of_perfectSecrecy`: **Shannon's bound**: perfect secrecy implies `H(M) ≤ H(K)`.
* `oneTimePad_perfectSecrecy`: the one-time pad has perfect secrecy, with `H(K) = H(M)` for a
  uniform message.
* `prob_key_le_of_perfectSecrecy`: for a key independent of a uniform message and a deterministic
  cipher, perfect secrecy implies `p(k) ≤ 1 / |𝓜|` for all `k`.
* `not_perfectSecrecy_of_entropy_ge`: `H(K) ≥ H(M)` alone does not suffice for a *given* key.

## Implementation notes

The notes state that `H(K) ≥ H(M)` is sufficient and necessary. The proof of sufficiency chooses the
key, which is uniform. For a key that is given, the condition is not sufficient, as
`not_perfectSecrecy_of_entropy_ge` shows.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010],
  Lecture 23
-/

open Real Finset

@[expose] public noncomputable section

namespace InfoTheory

section Bound

variable {Ω 𝓜 𝓚 𝓛 : Type*} [Fintype Ω] [Fintype 𝓜] [Fintype 𝓚] [Fintype 𝓛] {μ : Ω → ℝ}

/-- **Theorem 1 of Lecture 23 of [elgamal2010], page 23-3, necessity.** If the receiver recovers `M`
from the ciphertext `L` and the key `K`, and `I(M; L) = 0`, then `H(M) ≤ H(K)`. -/
theorem entropy_le_of_perfectSecrecy (hμ : IsPMF μ) (M : Ω → 𝓜) (K : Ω → 𝓚) (L : Ω → 𝓛)
    (dec : 𝓛 → 𝓚 → 𝓜) (hdec : ∀ ω, μ ω ≠ 0 → M ω = dec (L ω) (K ω))
    (hsec : I[M : L ; μ] = 0) : H[M ; μ] ≤ H[K ; μ] := by
  have h1 := mutualInfo_eq_entropy_sub_condEntropy hμ M L
  have h2 := chain_rule_cond hμ K M L
  have h3 : H[M | pair K L ; μ] = 0 :=
    (condEntropy_eq_zero_iff hμ _ _).2 ⟨fun w => dec w.2 w.1, hdec⟩
  have h4 := condEntropy_le_entropy hμ K L
  have h5 := chain_rule_cond hμ M K L
  have h6 : H[pair M K | L ; μ] = H[pair K M | L ; μ] :=
    condEntropy_congr_left hμ L Prod.swap Prod.swap_injective fun _ => rfl
  have h7 := condEntropy_nonneg hμ K (pair M L)
  linarith

end Bound

/-! ### The one-time pad -/

section Pad

variable {N : ℕ} [NeZero N]

/-- The law of a message with pmf `p` and an independent uniform key on `Fin N`. -/
def padLaw (p : Fin N → ℝ) : Fin N × Fin N → ℝ := fun z => p z.1 * (1 / N)

lemma padLaw_isPMF {p : Fin N → ℝ} (hp : IsPMF p) : IsPMF (padLaw p) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨fun z => mul_nonneg (hp.nonneg _) (by positivity), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [padLaw, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : ∀ m, (N : ℝ) * (p m * (1 / N)) = p m := fun m => by field_simp
  simp only [this, hp.sum_eq_one]

/-- **Page 23-4 of [elgamal2010].** The one-time pad `L = M + K` has perfect secrecy: the key is
uniform and independent of the message, the receiver recovers `M = L - K`, and `I(M; L) = 0`. -/
theorem oneTimePad_perfectSecrecy {p : Fin N → ℝ} (hp : IsPMF p) :
    I[Prod.fst : (fun z : Fin N × Fin N => z.1 + z.2) ; padLaw p] = 0 := by
  classical
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hμ := padLaw_isPMF hp
  rw [mutualInfo_eq_zero_iff hμ]
  intro m l
  have hm : dist (padLaw p) Prod.fst m = p m := by
    rw [dist_fst]
    simp only [padLaw, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hl : dist (padLaw p) (fun z : Fin N × Fin N => z.1 + z.2) l = 1 / N := by
    simp only [dist, padLaw]
    rw [Fintype.sum_prod_type]
    have : ∀ a : Fin N, ∑ b : Fin N, (if a + b = l then p a * (1 / (N : ℝ)) else 0) =
        p a * (1 / N) := fun a => by
      rw [sum_eq_single (l - a) (fun b _ hb => ite_eq_right_iff.2 fun h => (hb (by
        rw [← h]; abel)).elim) (by simp)]
      simp
    simp only [this]
    rw [← sum_mul, hp.sum_eq_one, one_mul]
  have hj : dist (padLaw p) (pair Prod.fst fun z : Fin N × Fin N => z.1 + z.2) (m, l) =
      p m * (1 / N) := by
    simp only [dist, pair, padLaw, Prod.mk.injEq]
    rw [Fintype.sum_prod_type, sum_eq_single m (fun a _ ha => sum_eq_zero fun b _ => by simp [ha])
      (by simp), sum_eq_single (l - m) (fun b _ hb => ite_eq_right_iff.2 fun h => (hb (by
        rw [← h.2]; abel)).elim) (by simp)]
    simp
  rw [hj, hm, hl]

/-- **Page 23-4 of [elgamal2010].** With a uniform message, the one-time pad uses a key with
`H(K) = H(M)`. -/
theorem oneTimePad_entropy :
    H[Prod.snd ; padLaw (uniformPMF (Fin N))] = H[Prod.fst ; padLaw (uniformPMF (Fin N))] := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have h₁ : dist (padLaw (uniformPMF (Fin N))) Prod.fst = uniformPMF (Fin N) := by
    funext m
    rw [dist_fst]
    simp only [padLaw, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h₂ : dist (padLaw (uniformPMF (Fin N))) Prod.snd = uniformPMF (Fin N) := by
    funext k
    rw [dist_snd]
    simp only [padLaw, uniformPMF, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [entropyRV, entropyRV, h₁, h₂]

end Pad

/-! ### A key with enough entropy need not suffice -/

section Given

variable {𝓚 𝓛 : Type*} [Fintype 𝓚] [Fintype 𝓛] {N : ℕ} [NeZero N]

/-- The law of a uniform message on `Fin N` and an independent key with pmf `ρ`. -/
def givenKeyLaw (ρ : 𝓚 → ℝ) : Fin N × 𝓚 → ℝ := fun z => 1 / N * ρ z.2

lemma givenKeyLaw_isPMF {ρ : 𝓚 → ℝ} (hρ : IsPMF ρ) : IsPMF (givenKeyLaw (N := N) ρ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨fun z => mul_nonneg (by positivity) (hρ.nonneg _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [givenKeyLaw, ← mul_sum, hρ.sum_eq_one, mul_one, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- If a deterministic cipher `c` has perfect secrecy for a uniform message on `Fin N` and an
independent key with pmf `ρ`, then every key has probability at most `1 / N`. The keys that lead to
a given ciphertext are disjoint for distinct messages, and each message has the same total. -/
theorem prob_key_le_of_perfectSecrecy {ρ : 𝓚 → ℝ} (hρ : IsPMF ρ) (c : Fin N → 𝓚 → 𝓛)
    (dec : 𝓛 → 𝓚 → Fin N) (hdec : ∀ m k, ρ k ≠ 0 → dec (c m k) k = m)
    (hsec : I[Prod.fst : (fun z : Fin N × 𝓚 => c z.1 z.2) ; givenKeyLaw ρ] = 0) (k₀ : 𝓚) :
    ρ k₀ ≤ 1 / N := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hμ := givenKeyLaw_isPMF (N := N) hρ
  have hind := (mutualInfo_eq_zero_iff hμ _ _).1 hsec
  set A : Fin N → 𝓛 → ℝ := fun m l => ∑ k, if c m k = l then ρ k else 0 with hA
  have hm : ∀ m, dist (givenKeyLaw (N := N) ρ) Prod.fst m = 1 / N := fun m => by
    rw [dist_fst]
    simp only [givenKeyLaw, ← mul_sum, hρ.sum_eq_one, mul_one]
  have hj : ∀ m l, dist (givenKeyLaw (N := N) ρ)
      (pair Prod.fst fun z : Fin N × 𝓚 => c z.1 z.2) (m, l) = 1 / N * A m l := fun m l => by
    simp only [dist, pair, givenKeyLaw, Prod.mk.injEq, hA, mul_sum]
    rw [Fintype.sum_prod_type, sum_eq_single m (fun a _ ha => sum_eq_zero fun b _ => by simp [ha])
      (by simp)]
    refine sum_congr rfl fun k _ => ?_
    simp
  have heq : ∀ m l, A m l = dist (givenKeyLaw (N := N) ρ) (fun z : Fin N × 𝓚 => c z.1 z.2) l :=
    fun m l => by
      have := hind m l
      rw [hj, hm] at this
      exact mul_left_cancel₀ (by positivity) this
  have hsum : ∀ l, (N : ℝ) * dist (givenKeyLaw (N := N) ρ) (fun z : Fin N × 𝓚 => c z.1 z.2) l ≤ 1 :=
    fun l => by
      obtain ⟨m₀⟩ : Nonempty (Fin N) := ⟨0⟩
      have e : (N : ℝ) * dist (givenKeyLaw (N := N) ρ) (fun z : Fin N × 𝓚 => c z.1 z.2) l =
          ∑ m, A m l := by
        simp only [heq _ l, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [e, ← hρ.sum_eq_one]
      simp only [hA]
      rw [sum_comm]
      refine sum_le_sum fun k _ => ?_
      by_cases hk : ρ k = 0
      · simp [hk]
      · by_cases hex : ∃ m, c m k = l
        · obtain ⟨m, hm'⟩ := hex
          rw [sum_eq_single m]
          · simp [hm']
          · intro b _ hb
            refine ite_eq_right_iff.2 fun h => (hb ?_).elim
            rw [← hdec b k hk, ← hdec m k hk, h, hm']
          · simp
        · push Not at hex
          simp [hex, hρ.nonneg k]
  obtain ⟨m₀⟩ : Nonempty (Fin N) := ⟨0⟩
  have h₁ : ρ k₀ ≤ A m₀ (c m₀ k₀) := by
    have := single_le_sum (f := fun k => if c m₀ k = c m₀ k₀ then ρ k else 0)
      (fun k _ => by split_ifs; exacts [hρ.nonneg k, le_rfl]) (mem_univ k₀)
    simpa using this
  rw [heq] at h₁
  have h₂ := hsum (c m₀ k₀)
  refine h₁.trans ?_
  rw [le_div_iff₀ hN]
  linarith

/-- The pmf `(3/4, 1/8, 1/8)` of a key. -/
def skewKey : Fin 3 → ℝ := ![3 / 4, 1 / 8, 1 / 8]

lemma skewKey_isPMF : IsPMF skewKey := by
  refine ⟨fun k => ?_, ?_⟩
  · fin_cases k <;> norm_num [skewKey]
  · simp [skewKey, Fin.sum_univ_three]
    norm_num

/-- The key `(3/4, 1/8, 1/8)` has entropy above one bit. -/
lemma log_two_le_entropy_skewKey : log 2 ≤ entropy skewKey := by
  have h₃ : (3 : ℝ) * log 3 ≤ 5 * log 2 := by
    have : log ((3 : ℝ) ^ 3) ≤ log ((2 : ℝ) ^ 5) := log_le_log (by norm_num) (by norm_num)
    simpa [log_pow] using this
  have e₁ : log (3 / 4 : ℝ) = log 3 - 2 * log 2 := by
    rw [log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have e₂ : log (1 / 8 : ℝ) = -(3 * log 2) := by
    rw [one_div, log_inv, show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    norm_num
  rw [entropy, Fin.sum_univ_three]
  simp only [skewKey, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, e₁, e₂]
  nlinarith

/-- **`H(K) ≥ H(M)` does not suffice for a given key.** The key `(3/4, 1/8, 1/8)` has more than one
bit of entropy, but no deterministic cipher has perfect secrecy for one uniform bit with this key,
since one of the keys has probability more than `1/2`. -/
theorem not_perfectSecrecy_of_entropy_ge (c : Fin 2 → Fin 3 → 𝓛) (dec : 𝓛 → Fin 3 → Fin 2)
    (hdec : ∀ m k, dec (c m k) k = m) :
    I[Prod.fst : (fun z : Fin 2 × Fin 3 => c z.1 z.2) ; givenKeyLaw skewKey] ≠ 0 := fun h => by
  have := prob_key_le_of_perfectSecrecy skewKey_isPMF c dec (fun m k _ => hdec m k) h 0
  norm_num [skewKey] at this

end Given

end InfoTheory
