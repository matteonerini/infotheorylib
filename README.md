# infotheorylib

[![Lean Action CI](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/matteonerini/infotheorylib/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-API-blue)](https://matteonerini.github.io/infotheorylib/docs/)

A Lean 4 library of information theory, built on [Mathlib](https://github.com/leanprover-community/mathlib4).

The goal is to formalize the core concepts and theorems of information theory, following
T. M. Cover and J. A. Thomas, *Elements of Information Theory* (2nd ed., Wiley, 2006), and
A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory* (arXiv:1001.3404, 2010), and
to organize them by topic, in the spirit of Mathlib for mathematics and Physlib for physics.

## Status

| Chapter of Cover & Thomas (2nd ed.) | Status |
|---|---|
| 1. Introduction and Preview | Formalized: all definitions and examples, with pointers to the later chapters for the announced results |
| 2. Entropy, Relative Entropy, and Mutual Information | Formalized: all definitions, lemmas, theorems, corollaries, remarks and examples |
| 3. Asymptotic Equipartition Property | Formalized: all definitions, theorems, remarks and examples, except convergence with probability 1 |
| 4. Entropy Rates of a Stochastic Process | Formalized: all definitions, lemmas, theorems, remarks and examples, including the second law of thermodynamics and hidden Markov models (see the chapter file for the facts quoted from later chapters) |
| 5. Data Compression | Formalized: all definitions, lemmas, theorems, corollaries and examples, except the Morse code example and the optimality of `D`-ary Huffman codes |
| 6. Gambling and Data Compression | Formalized: all definitions, theorems and examples, except the ergodic growth (6.37), proved in Chapter 16, and the experimental estimates of the entropy of English |
| 7. Channel Capacity | Formalized: all definitions, lemmas, theorems and examples, including both halves of the channel coding theorem, feedback capacity and source–channel separation; see the chapter file for the omitted remarks |
| 8. Differential Entropy | Formalized: all definitions, theorems, corollaries and examples, including the AEP for densities, the multivariate normal and Hadamard's inequality; Theorem 8.3.1 is proved for continuous compactly supported densities (see the chapter file for what is omitted) |
| 9. Gaussian Channel | Formalized: the information capacity and Theorem 9.1.1 (achievability and converse), the sampling theorem, bandlimited, parallel and colored-noise channels with water-filling, and Theorems 9.6.2–9.6.3 on feedback; Theorem 9.6.1 is not formalized (see the chapter file for what is omitted) |
| 10. Rate Distortion Theory | Formalized: all definitions, lemmas and theorems except Lemma 10.6.2, including the rate distortion theorem (achievability and converse), the Bernoulli source, the information rate distortion functions of Gaussian and parallel Gaussian sources (reverse water-filling), source–channel separation with distortion, strong typicality, and the Blahut–Arimoto algorithm without its convergence (see the chapter file for what is omitted) |
| 11. Information Theory and Statistics | Formalized: the method of types, the law of large numbers for types, universal source coding, Sanov's theorem, the Pythagorean theorem and Pinsker's inequality, the conditional limit theorem, the Neyman–Pearson and Chernoff–Stein lemmas, Chernoff information, and the Cramér–Rao inequality for finite parametric families (see the chapter file for what is omitted) |
| 12. Maximum Entropy | Formalized: Theorem 12.1.1 for densities and pmfs with uniqueness, all the examples of Section 12.2 (uniform, exponential, normal, Gibbs, multivariate normal, partial covariance constraints), and Burg's theorem 12.6.1 for finite segments with the entropy rate `½ log 2πeσ²`, assuming a solution of the Yule–Walker equations (see the chapter file for what is omitted) |
| 13. Universal Source Coding | Formalized: minimax redundancy equals capacity (Theorem 13.1.1, without the minimax theorem), two-stage and Laplace mixture codes for binary sequences, the probability integral transform and arithmetic coding intervals, the LZ77 and LZ78 algorithms with LZ78 decodability, Elias codes for the integers, Kac's lemma and the recurrence time code, and the optimality of LZ78 as deterministic bounds uniform over Markov models; the ergodic theorem is not formalized (see the chapter file for what is omitted) |
| 14. Kolmogorov Complexity | Formalized: computers as partial recursive functions with prefix-free programs, a universal computer constructed from Mathlib's universal partial recursive function, the universality of `K`, the upper and lower bounds of Section 14.2 with computable programs, `K` and entropy for Bernoulli sources (in expectation and in probability), the complexity of integers, incompressible sequences, universal probability, `Ω` and universal gambling, the noncomputability of `K`, and the easy half of Theorem 14.11.1 (see the chapter file for what is omitted) |
| 15. Network Information Theory | Formalized: the Gaussian multi-user formulas (onion peeling, frequency and time division, the broadcast and relay formulas), conditional joint typicality, the capacity region of the multiple-access channel (random coding with three typical groupings, time sharing, Lemma 15.3.1, the converse via Fano's inequality, Theorems 15.3.1–15.3.5), the Slepian–Wolf theorem (random binning and the converse), and the definitions of broadcast channels with Theorem 15.6.1 and degradedness (see the chapter file for what is omitted) |
| 16. Information Theory and Portfolio Theory | Formalized: growth rates and log-optimal portfolios for finite markets with positive price relatives, the Kuhn–Tucker conditions, the costs of wrong beliefs and the value of side information, causal strategies in market processes (the chain rule for `W*`, the supermartingale `Sₙ/Sₙ*`, the growth rate of stationary markets), almost sure growth and asymptotic optimality, competitive optimality, and finite-horizon universal portfolios (Theorem 16.7.1 for any number of stocks); see the chapter file for what is omitted |
| 17. Inequalities in Information Theory | Formalized: the `L₁` bound on entropy, the `χ²` approximation of relative entropy and the monotonicity of `E D(p̂ₙ‖p)`, the binomial bounds of Lemma 17.5.1, Han's inequalities (Theorems 17.6.1–17.6.4) for submodular set functions and discrete entropies, the determinant inequalities of Section 17.9 (Koteljanskii, Szász, Theorems 17.9.4–17.9.5, the Toeplitz theorem, Minkowski) and Bergstrøm's theorems of Section 17.10; de Bruijn's identity, the entropy power inequality and the Brunn–Minkowski and Young inequalities of Sections 17.7–17.8 are not formalized (see the chapter file for what is omitted) |

| Lecture of El Gamal & Kim | Status |
|---|---|
| 1. Introduction | Formalized: the notation (including the `DSBS(p)` pmf and the functions `C(x)` and `R(x)`), with pointers to Shannon's four theorems in Lecture 3 and the max-flow min-cut theorem in Lecture 16 |
| 2. Entropy, Mutual Information, and Typicality | Formalized: entropy, differential entropy and mutual information with their inequalities, Mrs. Gerber's lemma in the notes' `H⁻¹` form (scalar and vector), the Csiszár sum identity, robust typicality with the typical average lemma, the properties of jointly typical sequences, the conditional typicality lemma, joint typicality for Markov chains, the joint typicality lemma (parts 1 and 2), and weak typicality; the entropy power inequality, the conditional maximum differential entropy lemma and the Stirling appendix are not formalized (see the lecture file, which also lists the issues found in the notes) |
| 3. Point-to-Point Information Theory | Formalized: the channel coding theorem with the notes' definitions (rates in bits, average probability of error) and its examples, the packing lemma, channel coding with cost (Theorem 2), the AWGN channel (Theorem 3), lossless and lossy source coding with the Bernoulli examples and `R* = R(0)`, the covering lemma, the quadratic Gaussian rate–distortion function (Theorem 6, informational form), source–channel separation for `r = 1` and uncoded transmission; linear codes, Lemma 2 and the operational Gaussian source coding theorem are not formalized (see the lecture file) |
| 4. Multiple Access Channels | Formalized: the notes' definitions in bits, the time-division inner bound and the outer bound with `C₁`, `C₂`, `C₁₂`, the binary multiplier MAC (exact region) and the binary erasure MAC, the multi-letter characterization (Theorem 1), time sharing and convexity, the single-letter characterization (Theorem 2), the sum capacity, and the AWGN-MAC formulas (corner points, TDMA with power control); the cardinality bound \|Q\| ≤ 2 (Theorem 3), the AWGN-MAC coding theorem (Theorem 4) and the `k`-sender MAC (Theorem 5) are not formalized (see the lecture file) |
| 5. Degraded Broadcast Channels | Formalized: Lemma 1, time sharing, the simple bounds and their two examples, the superposition coding inner bound (Theorem 1), the capacity region of the degraded DM-BC (Theorem 2, without the cardinality bound), the capacity region of the binary symmetric BC, the capacity regions of less noisy and more capable channels, the BSC/BEC classification at exact thresholds; the common message, the AWGN-BC coding theorem (Theorem 3, which needs the entropy power inequality) and more than two receivers are not formalized (see the lecture file, which also lists the issues found in the notes) |
| 6. Interference Channels | Formalized: the problem setup, the simple and Sato outer bounds, the simultaneous decoding inner bound (with super-letters in place of coded time sharing), the channel with equal marginals as a MAC, the modulo-2 sum IC, very strong and strong interference with the example `Y₁ = Y₂ = X₁ + X₂`, Lemma 1 and the capacity region under strong interference (Theorem 1, up to closure, as `\|Q\|` is not bounded), and for the AWGN-IC the formulas only: the region of Theorem 2, the rectangle under very strong interference, the degrees of freedom with the redundant bound and the "W" shape. Not formalized: the Han–Kobayashi inner bound (Theorem 4), the deterministic and semideterministic ICs (Theorem 5, Lemma 3, Proposition 5), the AWGN-IC coding theorems (Theorems 2 and 3, the half-bit theorem), the `q`-ary expansion deterministic IC, more than two user pairs. |
| 7. Channels with State | Formalized: the compound channel (Theorem 1), also with the state at the decoder, with the compound BSC for finitely many crossover probabilities and the Z-channel example; the DMC with DM state in every scenario of state information: none, at the decoder, at both ends causally or noncausally, causally at the encoder (Theorem 3, Shannon strategies) and noncausally at the encoder (the Gelfand–Pinsker theorem, up to the cardinality bound); memory with defects and the BSC with additive state; for writing on dirty paper the formulas only: Costa's rate, its maximum `C(P)` and the corner point for the AWGN-MAC. Not formalized: infinitely many compound states, the arbitrarily varying channel (Theorem 2, stated without proof in the notes), the MAC and the degraded BC with state, writing on dirty paper as a coding theorem, coded state information. |
| 8. Fading Channels | Formalized for finitely many fading states: the slow-fading compound capacity `min_g C(g²P)` as a coding theorem, also with the gain at the encoder; the rest at the level of the formulas, as the notes mostly cite the proofs: water-filling in time with its optimality and the water level, the high-SNR limit, the outage and broadcasting metrics and their order, the MAC regions and sum capacities with their order, the BC regions, and for the fading IC the comparison of time division, treating interference as noise and interference alignment, with conjugate gain matrices and the pairwise converse step. Not formalized: the coding theorems of fast fading (ergodic capacities), general stationary ergodic gains, the operational meaning of the metrics, the Fourier–Motzkin elimination on page 8-19. |
| 9. General Broadcast Channels | Formalized for two receivers: the capacity region with degraded message sets (Theorem 1), the mutual covering lemma, Marton's inner bound (Theorem 2), also for random mappings `p(x \| u₁, u₂)`, the Cover–van der Meulen inner bound, the capacity regions of the semi-deterministic and deterministic channels, the outer bound with `U₂ = U`, the Blackwell channel and the formulas of the multilevel product example. Not formalized: the multilevel capacity region with indirect decoding (Theorem 5), Marton's bound with a common message (Theorem 3), the Nair–El Gamal outer bound in general (Theorem 4), the BSC–BEC and skew-symmetric examples, dirty paper coding for the AWGN-BC, and more than 2 receivers. The notes' region of the Blackwell channel is wrong, with a formal counterexample; see the lecture's index. |
| 10. Gaussian Vector Channels | Formalized: the capacity of the Gaussian vector channel as a coding theorem (Theorem 1), by rotating to parallel channels and coding along the singular directions; the rest at the level of the formulas: the SVD and water-filling, the reciprocity lemma, sufficiency of the KKT conditions, Theorem 2 for finitely many fading states with its low and high SNR limits, the GV-MAC and spectral BC regions, the fixed points of iterative water-filling, the MMSE formula for vector dirty paper, the MAC–BC duality `R_DPC = C_DMAC`, and the algebra of the enhanced degraded channel. Not formalized: the coding theorems for the GV-MAC (Theorem 3), the spectral BC, vector dirty paper and the GV-BC capacity (the second Theorem 4, whose Lemma 4 needs the vector entropy power inequality), the product of reversely degraded DM-BCs, the uniqueness of the supporting hyperplane, and more than two receivers. |
| 11. Distributed Lossless Source Coding | Formalized: the Slepian–Wolf theorem in bits, with the DSBS and the second example; lossless source coding with a helper (Theorem 2), with its achievability by covering and binning, its converse, and the region for the DSBS by Mrs. Gerber's lemma; and the Slepian–Wolf theorem for `k` sources (Theorem 3). Not formalized: random linear binning, zero-error coding, stationary ergodic sources, the cardinality bound on `U`, and Theorem 4. |
| 12. Source Coding with Side Information | Formalized: Theorem 1 (causal side information), the Wyner–Ziv theorem and Theorem 2 (lossless causal coding) as coding theorems, with the minimum attained for `\|𝒰\| ≤ \|𝒳\| + 3`; the cases of side information at the encoder or at both ends; `R_SI-ED ≤ R_SI-D ≤ R_CSI-D ≤ R`; the closed forms for the DSBS; and the formulas of the quadratic Gaussian case. Not formalized: the bound `\|𝒰\| ≤ \|𝒳\| + 1`, source coding when side information may be absent, and the coding theorems of the quadratic Gaussian case. |
| 13. Distributed Lossy Source Coding | Formalized: the Berger–Tung inner bound (Theorem 1) with the Markov lemma, Lemma 2, the mutual packing lemma and time sharing; the Berger–Tung outer bound (Theorem 2); the Wyner–Ziv and Slepian–Wolf special cases; and the formulas and algebra of the quadratic Gaussian and CEO problems. Not formalized: the cardinality bounds, the tightness statements, the DSBS counterexample, the Gaussian coding theorems (which need the conditional entropy power inequality), and more than two sources. |
| 14. Multiple Descriptions | Formalized: the Zhang–Berger inner bound (Theorem 4), proved by a conditional multivariate covering lemma with the codebooks chosen one layer at a time; the El Gamal–Cover inner bound (Theorem 1) as its special case with a time sharing variable; the simple outer bound with exact distortions; the three special cases; successive refinement (Theorem 3); Proposition 1; the Bernoulli example without excess rate; the successive refinability of a binary source; and the formulas and algebra of the quadratic Gaussian problem, including a counterexample showing that the formula of Theorem 2 as printed needs the condition `1/D₀ + 1/P ≥ 1/D₁ + 1/D₂`. Not formalized: the cardinality bound of Theorem 4, the convexity of the Zhang–Berger region and one inclusion of its alternative form, the tightness results cited from the literature, the Gaussian coding theorems (which need the conditional entropy power inequality), and more than two descriptions. |
| 15. Joint Source–Channel Coding | Formalized: the joint source–channel coding theorems for the DM-MAC (Theorem 2, for any common function, and Theorem 1 as its special case); the Gray–Wyner theorem (Theorem 3) with a cardinality bound; the common part, `K(U₁; U₂)` as the largest common rate, Wyner's `J(U₁; U₂)` as the smallest one, and `K ≤ I ≤ J ≤ H`; the binary example with `J = 2/3` bits, and the two examples where separation fails, over the binary erasure MAC and the Blackwell channel. Not formalized: Theorem 4 (Han–Costa) and Lemma 1, the separation results over the DM-BC, the DM-MAC with common message, the characterization of `K = I = J`, and the value of `J` for the DSBS. |
| 16. Noiseless Networks | Formalized: the max-flow min-cut theorem, both for flows with real and integer capacities and as a coding theorem achieved by routing; the case where every node wants the message; the network coding theorem by the method of Koetter and Médard, with Lemma 1, the determinant criterion, the size of the field and random linear codes; the capacity region of multi-source multicast networks; the cutset outer bound as a strong converse; and all the examples: the butterfly network (capacity `2`, and rate `3/2` for routing with copies at the source), its multiple unicast variant, and the network whose capacity region is strictly inside the cutset bound. Not formalized: networks with cycles (Lecture 19), the algorithms and complexity results cited, and the cited example where linear codes are suboptimal. |

The library contains no `sorry` and builds without warnings under Mathlib's linter set.

## Main results

A selection of the headline theorems; every result of the two texts is listed, with its Lean name,
in the chapter files `Books/CoverThomas/ChapterN.lean` and the lecture files
`Books/ElGamalKim/LectureN.lean`. Browse them
in the [API documentation](https://matteonerini.github.io/infotheorylib/docs/).

| Result (Cover & Thomas) | Lean declaration | Module |
|---|---|---|
| Data processing inequality (2.8.1) | `data_processing` | `MarkovChain.DataProcessing` |
| Fano's inequality (2.10.1) | `fano_estimator` | `Entropy.Fano` |
| Asymptotic equipartition property (3.1.1) | `aep` | `AEP.Basic` |
| Entropy rate of stationary processes (4.2.1) | `StochasticProcess.IsStationary.hasEntropyRate` | `StochasticProcess.Basic` |
| Kraft–McMillan inequality (5.5.1) | `kraft_of_isUniquelyDecodableCode` | `SourceCoding.Kraft` |
| Source coding bounds `H ≤ L* < H + 1` (5.4.1) | `minExpectedLength_bounds` | `SourceCoding.OptimalLength` |
| Optimality of Huffman codes (5.8.1) | `huffmanCode_optimal` | `SourceCoding.Huffman` |
| Channel coding theorem (7.7.1) | `isAchievableRate_of_lt_capacity`, `IsAchievableRate.le_capacity` | `ChannelCoding` |
| Feedback does not increase capacity (7.12.1) | `fbCapacity_eq_capacity` | `ChannelCoding.Converse` |
| Source–channel separation (7.13.1) | `exists_sourceChannelCode`, `entropyRate_le_capacity` | `ChannelCoding.SourceChannel` |
| Capacity of the Gaussian channel (9.1.1) | `gaussianOpCapacity_eq` | `GaussianChannel.Achievability` |
| Rate distortion theorem (10.2.1) | `rateDistortion_eq_infoRD` | `RateDistortion.Theorem` |
| Sanov's theorem (11.4.1) | `prob_typeEvent_le_sanov`, `tendsto_log_prob_typeEvent` | `Statistics.LargeDeviations` |
| Pinsker's inequality (11.6.1) | `pinsker` | `RelativeEntropy.Pinsker` |
| Chernoff–Stein lemma (11.8.3) | `tendsto_log_steinBeta` | `Statistics.HypothesisTesting` |
| Chernoff information (11.9.1) | `tendsto_neg_log_bayesErr` | `Statistics.ChernoffInformation` |
| Maximum entropy distributions (12.1.1) | `diffEntropy_le_of_eq_exp` | `MaxEntropy.Basic` |
| Minimax redundancy equals capacity (13.1.1) | `isLeast_maxRedundancy` | `SourceCoding.Minimax` |
| Kolmogorov complexity and entropy (14.3.1) | `tendsto_expected_complexity_div` | `Kolmogorov.Entropy` |
| Capacity region of the multiple-access channel (15.3.1) | `macCapacityRegion_eq` | `Network.MACCapacity` |
| Slepian–Wolf theorem (15.4.1) | `swAchievableRegion_eq` | `Network.SlepianWolf` |
| Universal portfolios (16.7.1) | `minimax_universal` | `Investment.Universal` |
| Han's inequality (17.6.1) | `subsetAvg_succ_le` | `Inequalities.Han` |
| Minkowski's determinant inequality (17.9.7) | `det_rpow_add_det_rpow_le` | `Inequalities.Determinant` |

| Result (El Gamal & Kim, lecture notes) | Lean declaration | Module |
|---|---|---|
| Mrs. Gerber's lemma (Lecture 2) | `binConv_binEntropyInv_le`, `binConv_binEntropyInv_le_prefixRV` | `Entropy.MrsGerber` |
| Csiszár sum identity (Lecture 2) | `csiszar_sum'` | `MutualInformation.CsiszarSum` |
| Typical average lemma (Lecture 2) | `card_mul_le_sum_of_mem_robustTypicalSet`, `sum_le_card_mul_of_mem_robustTypicalSet` | `Typicality.Basic` |
| Conditional typicality lemma (Lecture 2) | `one_sub_div_le_prob_condRobustTypicalSet` | `Typicality.Conditional` |
| Joint typicality lemma (Lecture 2) | `prob_condRobustTypicalSet_condDist_le`, `sum_mul_prob_condRobustTypicalSet_condDist_le` | `Typicality.JointTypicalityLemma` |
| Channel coding theorem (Lecture 3) | `opCapacityAvg_eq` | `ChannelCoding.AverageError` |
| Packing lemma (Lecture 3) | `prob_exists_mem_robustTypicalSet_le` | `Typicality.Packing` |
| Capacity with cost (Lecture 3, Theorem 2) | `opCapacityCost_eq` | `ChannelCoding.Cost` |
| Capacity of the AWGN channel (Lecture 3, Theorem 3) | `opCapacityAWGN_eq` | `GaussianChannel.AWGN` |
| Lossless source coding theorem (Lecture 3) | `optLosslessRate_eq` | `SourceCoding.LosslessRate` |
| Lossy source coding theorem (Lecture 3) | `rateDistortionBits_eq` | `RateDistortion.BitRate` |
| Covering lemma (Lecture 3) | `eventually_prob_forall_not_mem_robustTypicalSet_le` | `Typicality.Covering` |
| Multi-letter MAC capacity region (Lecture 4, Theorem 1) | `macCapacityRegionBits_eq_closure_iUnion` | `Network.MACMultiLetter` |
| MAC capacity region (Lecture 4, Theorem 2) | `macCapacityRegionBits_eq` | `Network.MACBits` |
| Superposition coding inner bound (Lecture 5, Theorem 1) | `superpositionRegionBits_subset` | `Network.BCSuperposition` |
| Capacity region of the degraded BC (Lecture 5, Theorem 2) | `bcCapacityRegionBits_eq_closure_degradedBCRegionBits` | `Network.BCCapacity` |
| Capacity region of the binary symmetric BC (Lecture 5) | `bcCapacityRegionBits_bsbc` | `Network.BCCapacity` |
| Sato's outer bound for the IC (Lecture 6) | `IsAchievableICBits.mem_closure_icSatoRegionBits` | `Network.ICBounds` |
| Simultaneous decoding inner bound for the IC (Lecture 6) | `icSimultaneousRegionBits_subset` | `Network.ICAchievability` |
| Capacity region of the IC under strong interference (Lecture 6, Theorem 1) | `icCapacityRegionBits_eq_closure_icStrongRegionBits` | `Network.ICAchievability` |
| Capacity of the compound channel (Lecture 7, Theorem 1) | `compoundCapacity_eq` | `StateChannel.Compound` |
| Capacity with causal state at the encoder, Shannon strategies (Lecture 7, Theorem 3) | `stateCapacity_causal_false` | `StateChannel.Causal` |
| Gelfand–Pinsker theorem (Lecture 7) | `stateCapacity_noncausal_false` | `StateChannel.GPConverse` |
| Compound capacity of the slowly fading Gaussian channel (Lecture 8) | `fadingCompoundCapacity_eq` | `GaussianChannel.FadingCompound` |
| Water-filling in time (Lecture 8) | `fadingPowerRate_le_of_waterFill` | `GaussianChannel.Fading` |
| Capacity region with degraded message sets (Lecture 9, Theorem 1) | `dmsCapacityRegionBits_eq` | `Network.BCDegradedMessages` |
| Mutual covering lemma (Lecture 9) | `eventually_sum_mutualCovering_typical_le` | `Typicality.MutualCovering` |
| Marton's inner bound (Lecture 9, Theorem 2) | `martonRegionBits_subset` | `Network.BCMarton` |
| Capacity region of the semi-deterministic BC (Lecture 9) | `bcCapacityRegionBits_eq_of_isSemiDeterministicBC` | `Network.BCSemiDeterministic` |
| Capacity region of the deterministic BC (Lecture 9) | `bcCapacityRegionBits_eq_of_isDeterministicBC` | `Network.BCCutSet` |
| Capacity of the Gaussian vector channel (Lecture 10, Theorem 1) | `opCapacityGV_eq` | `GaussianChannel.VectorCode` |
| Reciprocity lemma (Lecture 10) | `exists_reciprocal` | `GaussianChannel.Vector` |
| Isotropic fading: `K* = (P/t) I` (Lecture 10, Theorem 2) | `gvFadingCapacity_eq` | `GaussianChannel.VectorFading` |
| MAC–BC duality `R_DPC = C_DMAC` (Lecture 10) | `convexHull_dpcRegion_eq` | `Network.GaussianVector` |
| Slepian–Wolf theorem in bits (Lecture 11) | `swOptimalRegionBits_eq` | `Network.SlepianWolfBits` |
| Lossless source coding with a helper (Lecture 11, Theorem 2) | `helperOptimalRegionBits_eq` | `Network.SourceHelperConverse` |
| Slepian–Wolf theorem for `k` sources (Lecture 11, Theorem 3) | `manyOptimalRegionBits_eq` | `Network.SlepianWolfMany` |
| Rate–distortion with causal side information (Lecture 12, Theorem 1) | `rateCausalBits_eq` | `RateDistortion.SideInfoConverse` |
| Wyner–Ziv theorem (Lecture 12; 15.9.1) | `rateWZBits_eq` | `RateDistortion.SideInfoConverse` |
| Lossless source coding with causal side information (Lecture 12, Theorem 2) | `losslessCausalBits_eq` | `RateDistortion.SideInfoConverse` |
| Side information at both ends: `R_SI-ED(D) = min I(X; X̂ \| Y)` (Lecture 12) | `rateBothBits_eq` | `RateDistortion.SideInfoCases` |
| Markov lemma (Lecture 13) | `sum_not_mem_condRobust_le` | `Typicality.MarkovLemma` |
| Mutual packing lemma (Lecture 13) | `prob_mutual_packing_le` | `Network.BergerTungBinning` |
| Berger–Tung inner bound (Lecture 13, Theorem 1) | `isAchievableDL_of_lt_sharing` | `Network.BergerTungSharing` |
| Berger–Tung outer bound (Lecture 13, Theorem 2) | `IsAchievableDL.dlOuterAt` | `Network.BergerTungOuter` |
| Conditional multivariate covering lemma (Lectures 9 and 14) | `eventually_sum_two_codebooks_le` | `Network.MDCovering` |
| Zhang–Berger inner bound (Lecture 14, Theorem 4) | `isAchievableMD_zhangBerger` | `Network.ZhangBerger` |
| El Gamal–Cover inner bound (Lecture 14, Theorem 1) | `isAchievableMD_elGamalCover` | `Network.MDCases` |
| Simple outer bound for multiple descriptions (Lecture 14) | `mdRegion_subset_mdOuter` | `Network.MDOuter` |
| Successive refinement (Lecture 14, Theorem 3) | `mem_srRegion_iff` | `Network.MDCases` |
| Successively refinable sources (Lecture 14, Proposition 1) | `isSuccessivelyRefinable_iff` | `Network.MDCases` |
| Sources over a DM-MAC (Lecture 15, Theorems 1 and 2) | `isLosslessMAC_of_lt_time`, `isLosslessMAC_of_lt` | `Network.JSCCMAC` |
| Gray–Wyner theorem (Lecture 15, Theorem 3) | `gwRegion_eq` | `Network.GrayWynerConverse` |
| `K ≤ I ≤ J ≤ H` for the notions of common information (Lecture 15) | `common_information_chain` | `Network.CommonInformation` |
| Max-flow min-cut theorem, for flows (Lecture 16) | `maxFlow_minCut` | `ForMathlib.MaxFlow` |
| Max-flow min-cut theorem, for codes (Lecture 16) | `relay_capacity` | `Network.NoiselessRouting` |
| Network coding theorem (Lecture 16) | `network_coding_theorem` | `Network.NetworkCoding` |
| Capacity region of multi-source multicast networks (Lecture 16) | `capacityRegion_multisource` | `Network.NetworkCoding` |
| Cutset outer bound for noiseless networks (Lecture 16) | `IsAchievable.mem_cutsetRegion` | `Network.NoiselessCode` |

## Getting started

You need [elan](https://github.com/leanprover/elan). The Lean version is pinned in
`lean-toolchain` and Mathlib is pinned in `lakefile.toml`.

```sh
lake exe cache get   # download prebuilt Mathlib files
lake build           # build the library
```

### Using the library in your project

Add the library to the `lakefile.toml` of your project:

```toml
[[require]]
name = "infotheorylib"
git = "https://github.com/matteonerini/infotheorylib"
rev = "v4.36.0-rc2"
```

then run `lake update infotheorylib` and `lake exe cache get`. A Lake project can contain only one
version of Mathlib, so your project must use the same Lean toolchain (`v4.36.0-rc2`) and Mathlib
version as the release you depend on. Releases are tagged with the Lean version they support;
the available versions are listed on the
[releases page](https://github.com/matteonerini/infotheorylib/releases).
The library uses the module system, so it can be imported from both module and non-module files.

To use the library, import it and open the `InfoTheory` namespace, which also activates the
notation `H[X ; μ]`, `H[X | Y ; μ]`, `I[X : Y ; μ]` and `I[X : Y | Z ; μ]`:

```lean
import InfoTheoryLib

open InfoTheory

-- Conditioning reduces entropy (Theorem 2.6.5).
example {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β] {μ : Ω → ℝ} (hμ : IsPMF μ)
    (X : Ω → α) (Y : Ω → β) : H[X | Y ; μ] ≤ H[X ; μ] :=
  condEntropy_le_entropy hμ X Y

-- The same result, looked up by its number in Cover & Thomas.
#check @CoverThomas.theorem_2_6_5
```

## Layout

The library is organized by topic. Each file starts with a docstring listing its main
definitions and statements, and the book sections it covers.

```
InfoTheoryLib.lean                 root file, imports every module (generated by `lake exe mk_all`)
InfoTheoryLib/
  ForMathlib/          general facts not specific to information theory, to upstream to Mathlib
    Log.lean             logarithm and `negMulLog` lemmas, numerical bounds on log₂ 3 and log₂ 7
    Integral.lean        change of variables `∫ g(Ax) dx = |det A|⁻¹ ∫ g` for linear maps
    WeakLaw.lean         the weak law of large numbers for product measures
    MatrixDet.lean       determinant inequalities for positive semidefinite matrices
    MatrixSVD.lean       the singular value decomposition, the tangent bound and concavity of `log |A|`
    SupportLemma.lean    Carathéodory's theorem in the form of a support lemma
    MaxFlow.lean         flows, cuts and the max-flow min-cut theorem
    FlowDecomposition.lean  an integer flow on an acyclic network carries individual units
    PolyFiniteField.lean  nonzero polynomials over large finite fields, Schwartz–Zippel
    MatrixBlock.lean     block diagonal positive definite matrices
  Probability/         finite probability spaces
    FinitePMF.lean       pmfs (`IsPMF`), random variables, laws (`dist`), `AbsCont`, uniform pmf
    Event.lean           events and their probabilities `Pr{S}`
    Conditional.lean     conditional distributions `p(y | x)`
    Independence.lean    independence and conditional independence
    RandomVector.lean    random vectors `(X₀, …, X_{n-1})`, mutual independence
    Channel.lean         channels (transition kernels) `W(y | x)`
    Jensen.lean          Jensen's inequality
    Variance.lean        variance, Markov's and Chebyshev's inequalities
    IID.lean             i.i.d. sequences, the sample mean
    WeakLaw.lean         convergence in probability and in mean square, the weak law
  Analysis/
    LogSum.lean          the log sum inequality
  Entropy/
    Basic.lean           entropy `H(X)`, change of base
    Conditional.lean     conditional entropy `H(Y | X)`, chain rule
    ChainRule.lean       chain rule for random vectors
    Bounds.lean          `H(X) ≤ log |𝒳|`, conditioning reduces entropy, independence bound
    Concavity.lean       concavity of entropy
    Fano.lean            Fano's inequality
    Collision.lean       the probability `Pr(X = X')` that two independent variables agree
    MrsGerber.lean       Mrs. Gerber's lemma, scalar and vector, `H⁻¹` and binary convolution
  RelativeEntropy/
    Basic.lean           relative entropy `D(p ‖ q)`
    InformationInequality.lean  `D(p ‖ q) ≥ 0`
    Conditional.lean     conditional relative entropy, chain rule
    Convexity.lean       convexity of `D(p ‖ q)`
    Gibbs.lean           the Gibbs variational principle, tilted distributions
    Pinsker.lean         the `L₁` distance and Pinsker's inequality
  MutualInformation/
    Basic.lean           mutual information `I(X; Y)`
    Conditional.lean     conditional mutual information `I(X; Y | Z)`
    ChainRule.lean       chain rule for mutual information
    Convexity.lean       concavity and convexity of `I(X; Y)`
    CsiszarSum.lean      the Csiszár sum identity
  AEP/
    Basic.lean           the asymptotic equipartition property, sample entropy
    TypicalSet.lean      the typical set `A_ε^(n)` and its properties
    HighProbabilitySet.lean  smallest high-probability sets, `≐` (equality to first order)
    StrongTypicality.lean  strongly typical sequences, `Pr{A_ε^{*(n)}} → 1`
  Typicality/          robust typicality, as in El Gamal & Kim
    Basic.lean           the typical set `T_ε^(n)`, typical average lemma, properties 1–4
    Conditional.lean     jointly and conditionally typical sequences, conditional typicality lemma
    JointTypicalityLemma.lean  the joint typicality lemma, typicality for Markov chains
    Packing.lean         the packing lemma
    Covering.lean        the covering lemma
    MutualCovering.lean  the mutual covering lemma
    MarkovLemma.lean     the Chernoff bound, exponential conditional typicality, the Markov lemma
  StochasticProcess/
    Basic.lean           stochastic processes, stationarity, entropy rates
    Independent.lean     independent and i.i.d. processes
    Markov.lean          Markov chains as processes, the entropy rate of a Markov chain
    HiddenMarkov.lean    functions of Markov chains, hidden Markov models
    Recurrence.lean      recurrence times, Kac's lemma, the process of blocks
  SourceCoding/
    FixedLength.lean     fixed-length binary codes
    TypicalSetCode.lean  data compression with the typical set
    Code.lean            source codes: non-singular, uniquely decodable and prefix codes
    Kraft.lean           the Kraft and McMillan inequalities, finite and countable
    OptimalLength.lean   `L ≥ H_D(X)`, the Shannon code, optimal lengths, the wrong code
    Huffman.lean         Huffman codes and their optimality
    ShannonFanoElias.lean  Shannon–Fano–Elias coding
    ShannonFanoEliasBlock.lean  Shannon–Fano–Elias coding of sequences
    Competitive.lean     competitive optimality of the Shannon code
    CoinFlips.lean       generating discrete distributions from fair coin flips
    Universal.lean       universal source codes built from the method of types
    Minimax.lean         redundancy, minimax redundancy equals channel capacity
    BinarySequences.lean  two-stage and Bernoulli mixture codes, the Laplace estimate
    Arithmetic.lean      the probability integral transform, arithmetic coding intervals
    LempelZiv.lean       the LZ77 and LZ78 algorithms
    IntegerCode.lean     the Elias gamma and delta codes for the integers
    RecurrenceTime.lean  recurrence time coding, optimality of the idealized LZ77
    LempelZivOptimality.lean  Ziv's inequality, optimality of LZ78
    LosslessRate.lean    lossless source coding with vanishing error, `R* = H(X)`
  ChannelCoding/
    Capacity.lean        channel capacity, its properties, symmetric channels
    Code.lean            channel codes, error probabilities, achievable rates
    JointTypicality.lean  jointly typical sequences, the joint AEP
    Achievability.lean   random coding, the channel coding theorem (achievability)
    Converse.lean        Fano's inequality and the converse, zero-error codes, feedback capacity
    Hamming.lean         the (7, 4) Hamming code
    SourceChannel.lean   the joint source–channel coding theorem
    AverageError.lean    capacity with the average probability of error, rates in bits
    Product.lean         product channels, `C = C₁ + C₂`
    Cost.lean            channel coding with input cost, the capacity–cost function `C(B)`
  Gambling/
    HorseRace.lean       the horse race, doubling rate, proportional gambling, fair odds, cash
    SideInformation.lean  the value of side information, `ΔW = I(X; Y)`
    DependentRaces.lean  sequential betting on a stochastic process, doubling rate and entropy rate
    DataCompression.lean  data compression with a gambler and its identical twin
  MarkovChain/
    Basic.lean           Markov chains `X → Y → Z`
    Process.lean         Markov processes, stationary and doubly stochastic matrices
    DataProcessing.lean  the data processing inequality
    SecondLaw.lean       the second law of thermodynamics
    RandomWalk.lean      random walks on weighted graphs, reversibility
  DifferentialEntropy/
    Basic.lean           densities (`IsPDF`), differential entropy `h(f)`, translation and scaling
    AEP.lean             the AEP for continuous random variables, the typical set and its volume
    Quantization.lean    quantization, `H(X^Δ) + log Δ → h(X)`
    Joint.lean           joint and conditional differential entropy, mutual information `I(X; Y)`
    ChainRule.lean       chain rule for differential entropy, the independence bound
    RelativeEntropy.lean  relative entropy `D(f ‖ g)` of densities and `D(f ‖ g) ≥ 0`
    Gaussian.lean        entropy of the normal distribution, maximum entropy, estimation error
    MultivariateGaussian.lean  the multivariate normal `N(m, K)`, its entropy, Hadamard's inequality
    Partition.lean       mutual information of general random variables via finite partitions
    Estimation.lean      estimation error with side information
  GaussianChannel/
    Basic.lean           additive noise channels, bounding `I(X; Y)` by a reference output density
    Capacity.lean        the information capacity `½ log (1 + P/N)` of the Gaussian channel
    Code.lean            codes with a power constraint, error probabilities, achievable rates
    Converse.lean        the converse to the coding theorem
    Achievability.lean   random Gaussian codes, threshold decoding, Theorem 9.1.1
    Bandlimited.lean     the sampling theorem, the capacity `W log (1 + P/(N₀W))`
    WaterFilling.lean    water-filling
    Parallel.lean        parallel Gaussian channels
    ColoredNoise.lean    Gaussian channels with colored noise, the capacity `C_n`
    Feedback.lean        the capacity with feedback, `C_{n,FB} ≤ C_n + ½` and `C_{n,FB} ≤ 2C_n`
    AWGN.lean            the channel `Y = gX + Z` with rates in bits, `C = C(g²P)`
    FadingCompound.lean  the slowly fading channel, the compound capacity `min_g C(g²P)`
    Fading.lean          water-filling in time and the metrics of the fading channel, as formulas
    Vector.lean          the Gaussian vector channel: SVD, water-filling, reciprocity, KKT, MMSE
    VectorCode.lean      the coding theorem for the Gaussian vector channel, Theorem 1 of Lecture 10
    VectorFading.lean    Theorem 2 of Lecture 10 and the low and high SNR limits, as formulas
  RateDistortion/
    Basic.lean           distortion measures, rate distortion codes, `R(D)`, convexity of `R(D)`
    Converse.lean        the converse to the rate distortion theorem
    Achievability.lean   distortion typical sets, random coding, achievability
    Theorem.lean         the rate distortion region, `R(D) = R^(I)(D)`
    Binary.lean          the Bernoulli source, `R(D) = H(p) - H(D)`
    Gaussian.lean        the Gaussian source, `R(D) = ½ log (σ²/D)`, the function `R(x)`
    ParallelGaussian.lean  independent Gaussian sources, reverse water-filling
    SourceChannel.lean   source–channel separation with distortion
    BlahutArimoto.lean   `R(D)` as a double minimization, the Blahut–Arimoto algorithm
    BitRate.lean         rates in bits with `2^⌊nR⌋` indices, `R(0) = H(X)` for Hamming distortion
    SideInfo.lean        `R_CSI-D` and `R_SI-D` as single-letter functions: cardinality, minimum, convexity
    SideInfoCovering.lean  covering and random binning for typical triples
    SideInfoAchievability.lean  the codes of Lecture 12 and achievability
    SideInfoConverse.lean  Theorems 1 and 2 of Lecture 12 and the Wyner–Ziv theorem
    SideInfoCases.lean   side information at the encoder or at both ends, the inequalities
  Statistics/
    SufficientStatistic.lean  sufficient and minimal sufficient statistics
    Bernoulli.lean       Bernoulli trials, the number of ones as a sufficient statistic
    Types.lean           the method of types: types, type classes and their sizes
    LargeDeviations.lean  Sanov's theorem, the law of large numbers for types
    ConditionalLimit.lean  the Pythagorean theorem for `D`, the conditional limit theorem
    HypothesisTesting.lean  the Neyman–Pearson lemma, the Chernoff–Stein lemma
    ChernoffInformation.lean  the Bayesian error exponent, Chernoff information
    FisherInformation.lean  Fisher information and the Cramér–Rao inequality
  MaxEntropy/
    Basic.lean           Theorem 12.1.1, the maximum entropy distribution under moment constraints
    Distributions.lean   uniform, exponential, normal and Gibbs maximum entropy distributions
    Covariance.lean      maximum entropy under partial covariance constraints
    Burg.lean            AR(p) covariances, the Yule–Walker equations, Burg's theorem
  Kolmogorov/
    Computer.lean        computers, universal computers, Kolmogorov complexity, Kraft, counting
    Programs.lean        computable programs: printing a string, self-delimiting lengths
    BinaryStrings.lean   strings with `k` ones, `K(x | n) ≤ n H₀(k/n) + log n + c`
    Entropy.lean         `K` and entropy, integers, incompressible sequences
    UniversalProbability.lean  universal probability, Ω, universal gambling, the structure function
    Universal.lean       the construction of a universal computer
    Noncomputable.lean   the noncomputability of `K`
  Network/
    Gaussian.lean        Gaussian multiple-access, broadcast, relay and interference formulas
    Fading.lean          Gaussian fading MAC, BC and IC, as formulas
    Typicality.lean      conditional joint typicality, i.i.d. pairs, Theorem 15.2.2
    MACCode.lean         multiple-access codes, achievable rates, time sharing (Theorem 15.3.2)
    MACRegion.lean       the pentagons, the time-sharing region, Lemma 15.3.1
    MACAchievability.lean  random coding for the multiple-access channel
    MACConverse.lean     the converse for the multiple-access channel
    MACCapacity.lean     the capacity region, Theorems 15.3.1 and 15.3.4, corner points
    MACBits.lean         the MAC capacity region in bits, the pentagons `R(X₁, X₂)`
    MACBounds.lean       simple inner and outer bounds on the MAC region, the sum capacity
    MACMultiLetter.lean  the multi-letter characterization of the MAC region
    SlepianWolf.lean     distributed source codes, random binning, Theorem 15.4.1
    SlepianWolfBits.lean  the Slepian–Wolf theorem in bits
    SlepianWolfMany.lean  the Slepian–Wolf theorem for `k` sources
    SourceHelper.lean    source coding with a helper: random binning and achievability
    SourceHelperConverse.lean  source coding with a helper: the converse and the theorem
    BergerTung.lean      distributed lossy codes, the covering step of Berger–Tung coding
    BergerTungBinning.lean  the mutual packing lemma and the bound for random bins
    BergerTungInner.lean  the inner bound without time sharing
    BergerTungSharing.lean  time sharing and Theorem 1 of Lecture 13
    BergerTungOuter.lean  the outer bound, Theorem 2 of Lecture 13
    BergerTungCases.lean  the Wyner–Ziv and Slepian–Wolf cases of the inner bound
    QuadraticGaussian.lean  the formulas of the quadratic Gaussian and CEO problems
    MultipleDescriptions.lean  multiple description codes, the choice of one layer of codebooks
    MDCovering.lean      the covering bounds of the three layers of Zhang–Berger coding
    ZhangBerger.lean     the Zhang–Berger inner bound, Theorem 4 of Lecture 14
    MDOuter.lean         the simple outer bound
    MDCases.lean         the El Gamal–Cover inner bound, special cases, successive refinement
    MDGaussian.lean      the formulas of the quadratic Gaussian problem, Ozarow's theorem
    GrayWyner.lean       Gray–Wyner codes and the direct part of the theorem
    GrayWynerConverse.lean  the converse, the cardinality bound and Theorem 3 of Lecture 15
    CommonInformation.lean  the common part, the two notions of common information
    JSCCRandomCode.lean  the random coding bound for sources over a MAC, independent tables
    JSCCMACLaw.lean      the law of the scheme and the exponents of its error events
    JSCCMAC.lean         Theorems 1 and 2 of Lecture 15, uncoded transmission
    JSCCBC.lean          joint source–channel codes over a BC, uncoded transmission
    NoiselessCode.lean   noiseless networks, their codes and the cutset bound
    NoiselessRouting.lean  routing and the max-flow min-cut theorem
    LinearNetworkCode.lean  linear codes, the polynomial `|A(x)|`, the size of the field
    NetworkCoding.lean   the network coding theorem and multi-source multicast
    Broadcast.lean       broadcast codes, Theorem 15.6.1, degraded broadcast channels
    BCBits.lean          the BC in bits, the superposition and degraded regions
    BCTimeSharing.lean   BC codes, bits versus nats, Lemma 1, time sharing
    BCBounds.lean        simple inner and outer bounds on the BC region, two examples
    BCSuperpositionLaws.lean  the codebook laws and typical triples of superposition coding
    BCSuperposition.lean  the superposition coding inner bound
    BCDegradedLaws.lean  single-letter laws and time sharing for the degraded BC
    BCDegraded.lean      the converse for the degraded BC
    BinarySymmetricBC.lean  the binary symmetric BC and its region, via Mrs. Gerber's lemma
    BCClasses.lean       less noisy and more capable channels, the BSC and the BEC
    BCCapacity.lean      the capacity regions of the degraded and binary symmetric BC
    BCMoreCapableLaws.lean  single-code bounds, the Csiszár sum identity in telescoped form
    BCMoreCapable.lean   the converses for less noisy and more capable channels
    BCMarton.lean        Marton's inner bound, the Cover–van der Meulen inner bound
    BCCutSet.lean        the cut-set outer bound, the capacity region of the deterministic BC
    BCDegradedMessages.lean  degraded message sets, Theorem 1, the outer bound with `U₂ = U`
    BCSemiDeterministic.lean  Marton for random mappings, the semi-deterministic capacity region
    GaussianVector.lean  the GV-MAC regions, iterative water-filling, the MAC–BC duality
    GaussianVectorBC.lean  the enhanced degraded channel, the spectral Gaussian BC region
    ICCode.lean          interference channel codes, the capacity region, equal marginals as a MAC
    ICBounds.lean        Fano's inequality at each receiver, the simple and Sato outer bounds
    ICStrong.lean        strong interference, products of more capable channels, the converse
    ICSuperLetter.lean   compound random coding, independent letters as one super-letter
    ICAchievability.lean  coded time sharing by super-letters, the inner bound, Theorem 1
  StateChannel/
    Basic.lean           codes for the DMC with state, the scenarios, strategies, known state
    Multicoding.lean     random coding with subcodebooks, universal packing and covering bounds
    Compound.lean        the compound channel
    Causal.lean          causal state at the encoder, Shannon strategies
    GelfandPinsker.lean  the value I(U; Y) - I(U; S), achievability by multicoding
    GPDerandomize.lean   deterministic mappings x(u, s)
    GPConverse.lean      the converse, by the Csiszár sum identity, and the theorem
  Investment/
    Basic.lean           growth rates, log-optimal portfolios, concavity and convexity
    KuhnTucker.lean      the Kuhn–Tucker conditions, `E(S/S*) ≤ 1`
    SideInformation.lean  wrong beliefs and side information, `ΔW ≤ D(f‖g)` and `ΔW ≤ I(X; Y)`
    Causal.lean          causal strategies in market processes, the chain rule, stationary markets
    AlmostSure.lean      almost sure growth, asymptotic optimality, the sandwich lemma
    Competitive.lean     competitive optimality with fair randomization
    Universal.lean       universal portfolios, Theorem 16.7.1
  Inequalities/
    Han.lean             submodular set functions, Han's inequalities
    SubsetEntropy.lean   entropies of subsets of random variables, Theorems 17.6.1–17.6.4
    EntropyBounds.lean   the L₁ bound on entropy, the χ² approximation, `E D(p̂ₙ‖p)`
    Binomial.lean        bounds on binomial coefficients from Stirling's sequence
    Schur.lean           Schur complements, Fischer's inequality, Bergstrøm's theorems
    Determinant.lean     principal minors, Koteljanskii, Szász, Theorems 17.9.4–17.9.5, Minkowski
    Toeplitz.lean        determinants of Toeplitz matrices, Theorem 17.9.6
  Books/
   CoverThomas/        Cover & Thomas, namespace `InfoTheory.CoverThomas`
    Chapter1.lean        index of Chapter 1 (the preview), worked examples
    Chapter2.lean        index of Chapter 2, worked examples, aliases `theorem_2_6_5`, …
    Chapter3.lean        index of Chapter 3, worked examples, aliases `theorem_3_1_1`, …
    Chapter4.lean        index of Chapter 4, worked examples, aliases `theorem_4_2_1`, …
    Chapter5.lean        index of Chapter 5, worked examples, aliases `theorem_5_2_1`, …
    Chapter6.lean        index of Chapter 6, worked examples, aliases `theorem_6_1_1`, …
    Chapter7.lean        index of Chapter 7, worked examples, aliases `theorem_7_2_1`, …
    Chapter8.lean        index of Chapter 8, worked examples, aliases `theorem_8_2_1`, …
    Chapter9.lean        index of Chapter 9, worked examples, aliases `theorem_9_1_1`, …
    Chapter10.lean       index of Chapter 10, worked examples, aliases `theorem_10_2_1`, …
    Chapter11.lean       index of Chapter 11, worked examples, aliases `theorem_11_1_1`, …
    Chapter12.lean       index of Chapter 12, worked examples, aliases `theorem_12_1_1`, …
    Chapter13.lean       index of Chapter 13, worked examples, aliases `theorem_13_1_1`, …
    Chapter14.lean       index of Chapter 14, worked examples, aliases `theorem_14_2_1`, …
    Chapter15.lean       index of Chapter 15, worked examples, aliases `theorem_15_3_1`, …
    Chapter16.lean       index of Chapter 16, aliases `theorem_16_2_1`, …
    Chapter17.lean       index of Chapter 17, aliases `theorem_17_1_11`, …
   ElGamalKim/         El Gamal & Kim's lecture notes, namespace `InfoTheory.ElGamalKim`
    Lecture1.lean        index of Lecture 1 (the introduction), notation
    Lecture2.lean        index of Lecture 2, examples, aliases `mrs_gerber_lemma`, …
    Lecture3.lean        index of Lecture 3, examples, aliases `theorem_3_2`, `packing_lemma`, …
    Lecture4.lean        index of Lecture 4, binary MAC examples, aliases `theorem_4_1`, …
    Lecture5.lean        index of Lecture 5, the AWGN-BC region, aliases `theorem_5_1`, …
    Lecture6.lean        index of Lecture 6, modulo-2 sum IC, AWGN-IC formulas, `theorem_6_1`, …
    Lecture7.lean        index of Lecture 7, compound and defect examples, `gelfand_pinsker_theorem`
    Lecture8.lean        index of Lecture 8, the example with two fading states
    Lecture9.lean        index of Lecture 9, the Blackwell channel, the multilevel product example
    Lecture10.lean       index of Lecture 10, the product channel, beamforming to one antenna
    Lecture11.lean       index of Lecture 11, the DSBS, the helper for the DSBS
    Lecture12.lean       index of Lecture 12, lossless examples, the quadratic Gaussian case
    Lecture12DSBS.lean   the rate–distortion functions of Lecture 12 for the DSBS
    Lecture13.lean       index of Lecture 13
    Lecture14.lean       index of Lecture 14
    Lecture14Binary.lean  the binary examples of Lecture 14
    Lecture15.lean       index of Lecture 15
    Lecture15Examples.lean  the binary sources of Lecture 15: separation fails, `J = 2/3`
    Lecture16.lean       index of Lecture 16
    Lecture16Examples.lean  the butterfly networks and the linear code of Lecture 16
    Lecture16Yeung.lean  the network of Lecture 16 for which the cutset bound is loose
docs/
  references.bib       bibliography, cited in docstrings as `[cover2006]`
```

General theory goes in the topic folders, shared by both texts. Material that is specific to a
text (its worked examples, its numbering, text-only definitions) goes in
`Books/CoverThomas/ChapterN.lean` or `Books/ElGamalKim/LectureN.lean`, which also map each result of
the chapter or lecture to the declaration that proves it.

## Conventions

* Alphabets are finite (`Fintype`). A pmf is a function `p : α → ℝ` with `IsPMF p`, and a random
  variable is a function `X : Ω → α` on a finite probability space `(Ω, μ)`.
* From Chapter 8 on, continuous random variables are described by a density `f` with
  `IsPDF μ f` with respect to a reference measure `μ` (Lebesgue measure on `ℝ` or `ℝⁿ`).
  Differential entropies are Bochner integrals, so results assume the integrability of the
  relevant `f log f` terms.
* Logarithms are natural, so quantities are measured in nats. Statements in bits are obtained by
  dividing by `log 2`; the data compression results use `entropyBase D` (base `D`) directly.
* A stochastic process is given by its finite-dimensional laws (`StochasticProcess`). A code is a
  map `C : X → List α` into strings over a code alphabet `α`.
* `relEntropy` takes values in `[0, ∞]` (`EReal`); most results use the real-valued
  `relEntropyReal` under absolute continuity.
* Two notions of typicality coexist: the weak typicality of Cover & Thomas (`typicalSet`) and the
  robust typicality of El Gamal & Kim (`robustTypicalSet`); robustly typical sequences are weakly
  typical (`robustTypicalSet_subset_typicalSet`).

See [CONTRIBUTING.md](CONTRIBUTING.md) for the full conventions and the workflow for adding
files.

## Roadmap

Chapters 1–17 of Cover & Thomas are done: every chapter has a topic folder and a
`Books/CoverThomas/ChapterN.lean` index. The formalization of El Gamal & Kim's lecture notes is
in progress: Lectures 1–16 are done, and the remaining networks will reuse the typicality, packing
and covering lemmas of Lectures 2 and 3. The remaining work is
listed in the "Not formalized" section of each chapter file.

## How this library was made

The definitions, statements and proofs were written by Claude, an AI model by Anthropic, working
as a coding agent in Claude Code under the direction of Matteo Nerini, who chose the scope, the
conventions and the organization, and is responsible for the project.

What is guaranteed mechanically: every proof is checked by Lean's kernel; the library contains no
`sorry`; continuous integration builds it with warnings treated as errors; and axiom audits show
that every declaration depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

What is not guaranteed mechanically: that each Lean statement says what the corresponding
statement of the book says. The statements follow the book closely, and each chapter file lists
the conventions used and the deviations from the book, but before relying on a result, read its
Lean statement.

## Relation to Mathlib

Mathlib already contains some information theory in `Mathlib/InformationTheory/` (Hamming
distance, the Kraft–McMillan inequality, and the measure-theoretic Kullback–Leibler divergence
`InformationTheory.klDiv`), as well as `Real.binEntropy` and `Real.negMulLog`. This library
reuses them where possible. Connecting the finite `relEntropyReal` to `klDiv` is a natural step
before the continuous chapters. Lemmas in `ForMathlib/` are candidates for upstreaming.

## References

* T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006.
* A. El Gamal and Y.-H. Kim, *Lecture Notes on Network Information Theory*, arXiv:1001.3404, 2010.

## License

Released under the Apache 2.0 license, see [LICENSE](LICENSE).
