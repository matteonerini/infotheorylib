/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import InfoTheoryLib.Networking.AsyncMACAchievability
public import InfoTheoryLib.Networking.RandomAccess
public import InfoTheoryLib.Networking.RandomArrival

/-!
# El Gamal & Kim, Lecture 24: Information Theory and Networking

This file indexes the formalization of Lecture 24 of [elgamal2010], the last lecture of the notes.
We prove Lemma 1 and Theorem 1 on random data arrival at a DMC, Theorem 2 on the totally
asynchronous DM-MAC in both directions, and the formulas of the random access channel. Several
proofs in the notes have gaps, so some of ours are new (see "Differences from the notes").

## Conventions

* **Rates.** Rates are in bits, with `2 ^ ⌈n R⌉` messages, and informations are in nats.
* **Slots.** Slots and blocks are numbered from `0`, so block `j` starts at slot `j n`.
* **The queue.** The queue is real valued and a block carries `s` bits, with `s = nR` in Lemma 1 and
  `s = ⌈nR⌉` in Theorem 1, where a message has to be an integer number of bits.
* **Augmented codes.** The augmented message set is `Fin (M + 1)`, with `0` for the empty block.
* **Decoders.** The notes allow a decoder to declare an error, which does not help, so our decoders
  always return a message.
* **The asynchronous channel.** By stationarity, as the notes observe, one window of `2 n - 1`
  outputs with three messages per sender defines the error `P_e(d₁, d₂)`.
* **The random access channel.** The notes state the adaptive and broadcast regions without proof,
  so they are formalized as formulas, as in Lecture 8.

## Index

Module names are relative to `InfoTheoryLib`; "here" means this file.

### Random data arrival at a DMC (pages 24-2 to 24-6, 24-31 to 24-34)
* The queue (`Networking.Queue`): `queueOf`, `queueExp`, `queueMean`, `QueueStable`,
  `queueLowProb` (`p_j`).
* **Lemma 1:** `queueStable_of_lt` (sufficiency), `le_of_queueStable` (necessity), here
  `lemma_24_1_suff`, `lemma_24_1_nec`. The bound: `queueMean_iterate_le`.
* The drift: `serveOp`, `domOp`, `domOp_sq_le`, `domOp_iterate_mean_le`, `domOp_iterate_le_succ`,
  `serveOp_iterate_le_domOp`.
* Finite buffers: `queue_tail_le`.
* The served fraction: `queueMean_succ`, `exists_one_sub_queueLowProb_ge`.
* The chain can be periodic: `queueMean_not_tendsto`.
* The code (`Networking.RandomArrival`): `arrivalErr` (`P_ej`), `IsReliableArrival`.
* **Theorem 1:** `isReliableArrival_of_lt`, `exists_isReliableArrival`,
  `IsReliableArrival.le_capacity`, here `theorem_24_1_achievability`, `theorem_24_1_converse`.
* The strict inequality of the converse fails: `printed_theorem1_strict_false`.

### The asynchronous DM-MAC (pages 24-7 to 24-22, 24-35 to 24-37)
* The model (`Networking.AsyncMAC`): `asyncInput`, `AsyncCode`, `AsyncCode.asyncErr`,
  `IsAchievableAsync`, `asyncCapacityRegionBits`, `asyncRegionBits`, `isClosed_asyncRegionBits`.
* The converse (`Networking.AsyncMACConverse`): `cycInput`, `cycWindow`, `AsyncCode.cycCode`,
  `AsyncCode.avgErrProb_cycCode_le`, `sum_cyc_eq`, `avgLaw`, `sum_macInfo₁_le`, `sum_macInfo₂_le`,
  `sum_macInfo₁₂_le`, `AsyncCode.log_le_of_asyncErr_le`, `IsAchievableAsync.mem_asyncRegionBits`,
  `asyncCapacityRegionBits_subset`.
* The random tables (`Networking.AsyncTable`): `tableLaw`, `sum_tableLaw_update`,
  `sum_tableLaw_prod_le`, `infoRatio`, `sum_tables_prod_le`, `sum_tables_test_le`,
  `sum_tables_halves_le`, `sum_tables_fail_le`, `exists_chernoff`.
* The slots (`Networking.AsyncWindow`): `asyncPos`, `asyncOff`, `asyncSeg`, `asyncMsg`, `asyncTest`,
  `asyncPos_inj`, `le_card_filter_segA`, `le_card_filter_segB`, `asyncOff_eq_of_seg_eq`,
  `asyncPos_shift_unique`.
* The decoder (`Networking.AsyncDecoder`): `asyncLetter`, `AsyncPasses`, `AsyncAccepts`,
  `asyncDecA`, `asyncPasses_fresh_le`, `asyncPasses_conflict_le`, `asyncPasses_true`.
* The union bound (`Networking.AsyncError`): `exists_asyncMGF_le`, `asyncE_fail_le`,
  `card_fresh_fiber_le`, `async_exponent_le`, `sum_asyncE_passes_le`.
* The achievability (`Networking.AsyncMACAchievability`): `asyncE_decA_le`, `asyncTableCode`,
  `exists_asyncCode`, `isAchievableAsync_of_lt`.
* **Theorem 2:** `asyncCapacityRegionBits_eq`, here `theorem_24_2`.
* The preambles can fail: here `rac_adder_preamble`.

### The random access channel (pages 24-23 to 24-28; `Networking.RandomAccess`)
* `racOutput`, `racW`.
* The compound region: `IsAchievableRACCompound`, `isAchievableRACCompound_iff`.
* The adaptive region: `racAdaptiveRegion`, `mem_racAdaptiveRegion_iff`, `racAvgSum`,
  `isGreatest_racAvgSum`.
* The broadcast approach: `racBCRegion`, `racBCSum`, `isGreatest_racBCSum`.
* The ergodic sum capacity: `isGreatest_racErgodic`.
* The comparison of the sum capacities: `racSum_comparison`, `racBC_gt_iff`.

## Differences from the notes

* **Lemma 1, sufficiency.** The notes bound the Cesàro means of `E Q̃_j` by a drift argument, and
  then use the convergence of a positive recurrent aperiodic chain. We apply the same drift to a
  monotone chain dominating the queue, whose mean started at `0` is nondecreasing, so that the bound
  on the Cesàro means bounds the means. This needs no ergodic theory, and it holds for `p = 1` too.
* **Theorem 1, converse.** We add the missing step: a stable queue has
  `P{M_j ≠ 0} ≥ λ / (2 (R + 1))` for some block `j`, by balancing arrivals and departures, and only
  then does `P_ej → 0` control the error of the nonzero messages. We need `p > 0` and `k > 0`, as
  the conclusion `R ≤ C` fails if no data arrives.
* **Theorem 2, converse.** The notes decode `κ` blocks from a long sequence, assume that
  communication started in the remote past to ignore the edges, and let `κ → ∞`. We run the code
  cyclically on three blocks, which has no edges and is an ordinary code for the synchronous DM-MAC,
  so that `κ = 3` suffices and no limit is needed. The uniform delay `D₂` and the variable `Q` of
  the notes appear as the average over independent positions of the two senders.
* **Theorem 2, achievability.** We prove it differently, because the proof in the notes has gaps
  (see "Issues in the notes"). There are no preambles for synchronization. A block has pilot
  segments at both ends, to align the test set with the segments of the other sender, and the
  decoder searches jointly over the delays and the messages. Each position of a block has its own
  independent letters. Each group of slots has its own information-density test, and a change of
  measure replaces the joint typicality lemma. A hypothesis that reuses a sub-message actually sent
  is excluded by splitting its slots into two classes without conflicts, which is the idea of Lemma
  2.
* **All block lengths.** The notes take `n = (b + 1) k`. We cover every large `n`, with a longer
  pilot.

## Not formalized

* The extension of Theorem 1 to the DM-MAC (`𝒮 = 𝒞`), which the notes say "can be readily shown". It
  is not immediate: the converse needs a block in which both senders are active with probability
  bounded below, which the fractions of active blocks of the two queues do not give directly.
* The remark on correlated packet arrivals.
* The slightly asynchronous case and the remark on the AWGN-MAC, both stated without proof.
* Lemma 2 as stated, which the new proof replaces by `asyncPasses_conflict_le`.
* The operational meaning of the adaptive and broadcast regions of the random access channel, and of
  its ergodic sum capacity, all stated without proof.
* The figure on page 24-28, beyond the inequalities `racSum_comparison` and `racBC_gt_iff`.

## Issues in the notes

* **Page 24-5, Theorem 1.** The converse claims `λ < R`, but Lemma 1 only gives `λ ≤ R`, and the
  claim is false for `p = 1`, which the notes allow: `printed_theorem1_strict_false`. The proof on
  the same page says "we already know that we must have `R > λ`".
* **Page 24-5, converse of Theorem 1.** Fano's inequality conditionally on `M_j ≠ 0` needs
  `P{M_j ≠ 0}` bounded away from `0`, which the notes do not address.
* **Page 24-33.** "It can be readily checked that the Markov chain is aperiodic (why?)" fails for
  `p = 1`, where the mean backlog can oscillate: `queueMean_not_tendsto`.
* **Pages 24-3 and 24-31.** The indices of the transition law are inconsistent. The queue is
  inspected at time `jn` on both pages, which is the end of block `j` in the numbering of the
  appendix, while the recursion for `Q̃_j = Q((j - 1) n + 1)` on page 24-32 tests `Q̃_j`, at the
  beginning of the block.
* **Page 24-4.** The conditional error in `P_ej` should be conditioned on `M_j = m`, not `M_j ≠ 0`.
* **Page 24-8.** The code should be `(2^{nR₁}, 2^{nR₂}, n, d)`, not `(2^{nR₂}, 2^{nR₂}, n, d)`.
* **Page 24-15: synchronization.** Lemma 2 assumes `p(x, y) ≠ p(x) p(y)`, an assumption Theorem 2
  does not have, and the notes do not say what to do when it fails. It does fail: on the binary
  adder, if `X₁` is uniform then `X₂` is independent of `Y`, whatever its law (`rac_adder_preamble`
  for uniform inputs), and the sum rate `1` needs one input to be uniform. So sender 2 has no
  detectable preamble for these inputs. Perturbing the inputs might repair this, but it would need
  an argument.
* **Pages 24-16 to 24-19: the error patterns.** The test is joint typicality of the whole block, but
  the bound uses the joint typicality lemma on each of the groups `k₁, …, k₄`. Typicality of the
  whole block does not imply typicality of each group, so the exponent does not follow.
* **Page 24-19.** "All erroneous messages must be different (otherwise they would be detected…)" is
  not justified: a wrong message sequence can repeat a wrong message. Then the symbols of a group
  are not independent.
* **Pages 24-14 to 24-19.** The notes bound the error averaged over the codebooks for each pair of
  delays. One code good for all `n²` pairs needs a union bound, but the terms that "→ 0 by the LLN"
  have no rate.
* **Page 24-14.** The typical set `T_ε^{(n)}` is used for sequences of length `k`.
* **Page 24-24.** The bounds on `R₂₀` and `R₂₁` should use `I(X₂; Y | X₁, …)`, not
  `I(X₁; Y | X₂, …)`. As printed, `R₂₁ ≤ I(X₁; Y | X₂, s₁ = 0, s₂ = 1) = 0`, against the conclusion
  on the next page.
* **Page 24-25.** "`R₁₁ = 1 - R₂₁`" holds only on the boundary, and the average sum rate omits the
  term of `s₁ = s₂ = 0`, which vanishes.
* **Page 24-35.** The sum defining `π(x, y | X^k, Y)` is missing the factor `1 / k`.
* **Page 24-36.** The sentence "as `n → ∞`, where" is unfinished.

## References

* [A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*][elgamal2010], Lecture
  24
-/

open Real

@[expose] public noncomputable section

namespace InfoTheory

namespace ElGamalKim

/-! ### The preambles can fail -/

/-- **The preambles of the notes can fail.** On the binary adder `Y = X₁ ⊕ X₂` with uniform inputs,
`I(X₁; Y | X₂) = I(X₂; Y | X₁) = 1` bit while `X₁` and `X₂` are each independent of `Y`, so that the
assumption `p(x, y) ≠ p(x) p(y)` of Lemma 2 fails. -/
theorem rac_adder_preamble :
    macInfo₁ (uniformPMF Bool) (uniformPMF Bool) (racW true true) = log 2 ∧
    macInfo₂ (uniformPMF Bool) (uniformPMF Bool) (racW true true) = log 2 ∧
    I[Prod.snd : fun z : (Bool × Bool) × Bool => z.1.2 ;
      macJoint (uniformPMF Bool) (uniformPMF Bool) (racW true true)] = 0 ∧
    I[Prod.snd : fun z : (Bool × Bool) × Bool => z.1.1 ;
      macJoint (uniformPMF Bool) (uniformPMF Bool) (racW true true)] = 0 := by
  have hu : IsPMF (uniformPMF Bool) := uniformPMF_isPMF
  have hW := racW_isChannel true true
  have h1 := macInfo₁_rac_uniform true
  have h2 := macInfo₂_rac_uniform true
  have h3 := macInfo₁₂_rac_uniform (s₁ := true) (s₂ := true) (Or.inl rfl)
  have h4 := macInfo₁₂_eq_add₁ hu hu hW
  have h5 := macInfo₁₂_eq_add₂ hu hu hW
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h3, h1] at h4
    linarith
  · rw [h3, h2] at h5
    linarith

/-! ### Aliases -/

section Aliases

variable {α β : Type*} [Fintype α] [Fintype β] {W : α → β → ℝ}

/-- **Lemma 1 of Lecture 24 of [elgamal2010], sufficiency.** If `λ < R`, the queue is stable. -/
theorem lemma_24_1_suff {p R : ℝ} {k n : ℕ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n)
    (h : p * k < R) : QueueStable p k n (n * R) :=
  queueStable_of_lt h0 h1 hn (mul_lt_mul_of_pos_left h (by exact_mod_cast hn))

/-- **Lemma 1 of Lecture 24 of [elgamal2010], necessity.** If the queue is stable, then `λ ≤ R`. -/
theorem lemma_24_1_nec {p R : ℝ} {k n : ℕ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (hn : 0 < n) (hR : 0 ≤ R)
    (h : QueueStable p k n (n * R)) : p * k ≤ R := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact le_of_mul_le_mul_left (le_of_queueStable h0 h1 hn (by positivity) h) hn'

/-- **Theorem 1 of Lecture 24 of [elgamal2010], achievability.** If `λ < C`, the arrivals can be
reliably communicated. -/
theorem theorem_24_1_achievability [Nonempty α] (hW : IsChannel W) {p : ℝ} {k : ℕ}
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (h : p * k * log 2 < capacity W) : ∃ R, IsReliableArrival W p k R :=
  exists_isReliableArrival hW h0 h1 h

/-- **Theorem 1 of Lecture 24 of [elgamal2010], converse**, with `λ ≤ R` for the printed `λ < R`. -/
theorem theorem_24_1_converse [Nonempty α] (hW : IsChannel W) {p R : ℝ} {k : ℕ} (h0 : 0 < p)
    (h1 : p ≤ 1) (hk : 0 < k) (h : IsReliableArrival W p k R) :
    p * k ≤ R ∧ R * log 2 ≤ capacity W :=
  h.le_capacity hW h0 h1 hk

/-- **Theorem 2 of Lecture 24 of [elgamal2010].** The capacity region of the totally asynchronous
DM-MAC. -/
theorem theorem_24_2 {α₁ α₂ : Type*} [Fintype α₁] [Fintype α₂] [Nonempty α₁] [Nonempty α₂]
    {W : α₁ × α₂ → β → ℝ} (hW : IsChannel W) :
    asyncCapacityRegionBits W = asyncRegionBits W :=
  asyncCapacityRegionBits_eq hW

end Aliases

end ElGamalKim

end InfoTheory
