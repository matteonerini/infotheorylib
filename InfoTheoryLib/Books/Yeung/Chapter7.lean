/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

/-!
# Yeung, Chapter 7: Discrete Memoryless Channels

This file maps Chapter 7 of [yeung2008] to the library. It cites the draft of 15 November 2007,
which numbers definitions, theorems and examples with one counter per chapter. No aliases are
defined yet, and the end-of-chapter problems and the historical notes are not included.

Module names are relative to `InfoTheoryLib`.

## In the library

* Definition 7.1: `IsChannel` (`Probability.Channel`).
* Definition 7.4: `channelExt` (`ChannelCoding.Code`).
* Definition 7.6: `capacity`, `exists_capacity_eq` (`ChannelCoding.Capacity`).
* Example 7.7 (Binary Symmetric Channel): `capacity_bsc` (`Books.CoverThomas.Chapter7`).
* Example 7.8 (Binary Erasure Channel): `capacity_bec` (`Books.CoverThomas.Chapter7`).
* Definition 7.9: `ChannelCode` (`ChannelCoding.Code`).
* Definition 7.10: `ChannelCode.condErrProb` (`ChannelCoding.Code`).
* Definition 7.11: `ChannelCode.maxErrProb` (`ChannelCoding.Code`).
* Definition 7.12: `ChannelCode.avgErrProb` (`ChannelCoding.Code`).
* Definition 7.18: `FeedbackCode` (`ChannelCoding.Converse`).

## Partly in the library

* Definition 7.14: `IsAchievableRate` (`ChannelCoding.Code`). Other definition, with a rate of
  exactly R.
* Theorem 7.15 (Channel Coding Theorem): `isAchievableRate_of_lt_capacity`,
  `IsAchievableRate.le_capacity`, `opCapacity_eq_capacity` (`ChannelCoding.Achievability`,
  `ChannelCoding.Converse`). The book's definition also gives R = C.
* Lemma 7.16: `mutualInfo_channelExt_le` (`ChannelCoding.Converse`). The bound by nC, not by the sum
  of the informations of the letters.
* Lemma 7.17: `prob_indep_jointTypicalSet_le`, `eventually_prob_indep_jointTypicalSet_ge`
  (`ChannelCoding.JointTypicality`). For weak typicality.
* Definition 7.19: `IsAchievableRateFB` (`ChannelCoding.Converse`). Other definition, as for
  Definition 7.14.
* Definition 7.20: `fbCapacity` (`ChannelCoding.Converse`). Other definition, as for Definition
  7.14.

## Other material

* Section 7.7, separation of source and channel coding: `exists_sourceChannelCode`,
  `entropyRate_le_capacity` (`ChannelCoding.SourceChannel`).

## To formalize

* Definition 7.2
* Definition 7.3
* Definition 7.5
* Definition 7.13
* Proposition 7.21
* Lemma 7.22
* Example 7.23

## References

* [R. W. Yeung, *Information Theory and Network Coding*][yeung2008], Chapter 7
-/
