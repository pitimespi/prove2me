# NOTES — `OpenSearchElectionTimer`: randomized election timers

Mission over OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java` (cited `ESF:<line>`), built
on the scheduler transcription of the pre-voting mission (`OpenSearchPreVote`, see `../NOTES_OpenSearchCoordination.md`).
7 theorems, all proved. Mathlib is used for finite sums, cardinalities and rational arithmetic; there is no measure
theory: probabilities are counts.

- Model: `Definitions/Def_OpenSearchElectionTimer.lean` (imports `Mathlib` and `Definitions.Def_OpenSearchPreVote`).
  `Definitions/Def_OpenSearchPreVote.lean` and `Definitions/Def_OpenSearchCoordination.lean` in this workspace are
  copies of the main project's files. `Def_OpenSearchCoordination.lean` is identical (checked with `diff`);
  `Def_OpenSearchPreVote.lean` differs only in the docstring of `handleJoins` (lines 141-144 here, 141-145 in the main
  project), which this mission does not use.
- Proofs: `Solutions/Sol_OpenSearchElectionTimer_all.lean` (7 public theorems); the 7 split files
  `Solutions/Sol_OpenSearchElectionTimer_<name>.lean` and the statement stubs `Theorems/Thm_OpenSearchElectionTimer_<name>.lean`.
- Prose: `../missions/items/ostimer_items.py`, `../missions/descriptions/ostimer_description.md`,
  `../missions/explanations/expl_OpenSearchElectionTimer_*.md` (one per theorem).
- Goal theorem: `OpenSearchElectionTimer.all_contested_prob_le` (`K` rounds are all contested with probability at most
  the `K`-th power of the per-round bound, even against an adaptive scheduler; exponentially small once that bound is
  below 1); the items leave no milestone on it.

Citations: `ESF` ElectionSchedulerFactory.java and `CO` Coordinator.java (same directory), `DiscoveryModule.java`
(`server/src/main/java/org/opensearch/discovery/`), with line numbers at the pinned revision.

## The Java behaviour

A node starts an election scheduler when it is a cluster-manager-eligible candidate whose discovered peers, with
itself, could form an election quorum, and closes it otherwise (`onFoundPeersUpdated`, CO:1534-1550;
`startElectionScheduler`, CO:1567-1618); a node that has just bootstrapped starts one too (CO:1158). The scheduler's
attempt `k` (counted from 0) is scheduled with delay `toPositiveLongAtMost(random.nextLong(), maxDelay) + gracePeriod`
(ESF:204), where `maxDelay = min(maxTimeout, initialTimeout + k · backoffTime)` (ESF:203) and
`toPositiveLongAtMost(r, M) = nonNegative(r) % M + 1` (ESF:169-172). The grace period is 0 for the first attempt
(CO:1574); when attempt `k` fires it schedules attempt `k + 1` with grace period `cluster.election.duration` (ESF:218)
and, if the node is still a candidate that may win, is healthy and is not decommissioned, starts a new pre-voting round,
closing the previous one (CO:1578-1608). Defaults: `initial_timeout` 100 ms, `back_off_time` 100 ms, `max_timeout`
10 s, `duration` 500 ms (ESF:85-115). The documentation (ESF:71-83) says the delay is chosen uniformly from
`(0, maxDelay]`.

`random` is the node's `Random`, created once per node as `new Random(Randomness.get().nextLong())`
(DiscoveryModule.java:213), handed to the scheduler factory by the `Coordinator` (CO:262-263) and also used by the
`Coordinator` to choose a node to abdicate to (`random.nextInt`, CO:1818).

## The model

- `toLong x = x − 2^63` for `x : Fin (2^64)`: the `2^64` values of `nextLong()` as elements of `Fin (2^64)`.
- `randomDelay M x = toPositiveLongAtMost (toLong x) M`: the random part of the delay (ESF:204).
- `fireTime offset bound x i = offset i + randomDelay (bound i) (x i)` for `n` candidates `i : Fin n`, with
  `offset : Fin n → ℤ` (when the timer was started, plus the grace period) and `bound : Fin n → ℕ` (the attempt's
  `maxDelay`).
- `Uncontested offset bound δ x`: some `i` with `fireTime i + δ ≤ fireTime j` for every `j ≠ i` (decidable).
- `contestedBound n δ Mmin = C(n,2) · (2δ − 1) · ⌈2^63/Mmin⌉ / 2^63` in `ℚ`, with `2δ − 1` in `ℕ` and the ceiling as
  `(2^63 + Mmin − 1) / Mmin` in `ℕ`.
- A probability is a cardinality divided by `(2^64)^n` (one round, draws `Fin n → Fin (2^64)`) or `(2^64)^(n K)` (`K`
  rounds, draws `Fin K → Fin n → Fin (2^64)`): uniform, independent draws.

Offsets are arbitrary integers and bounds arbitrary naturals between `Mmin` and `2^63`. So the theorems apply whatever
the attempt numbers, grace periods and start times of the candidates' schedulers, including candidates at different
attempt numbers in the same round, with `Mmin` at most the smallest competing `maxDelay`; the bound is at least 1, and
says nothing, unless that minimum exceeds about `C(n, 2)(2δ − 1)`, and it is small only when the minimum is much larger
(see Numbers). Reading `offset` as start time plus grace period and `bound` as `maxDelay` is informal: no definition or
theorem statement of this mission mentions `maxDelay`, `SchedulerSettings`, `attemptDelay` or a grace period. In
`all_contested_prob_le` the offsets and bounds of round `k` are any
functions of the draws of the rounds before `k` (`hcausal`): an adversary scheduling the network may react to everything
drawn so far, but not to the draws of round `k` or later.

## Public theorems

In file order, which is also a dependency order (each theorem's proof uses only earlier ones):

- `randomDelay_range` (`1 ≤ M`): `1 ≤ randomDelay M x ≤ M`.
- `randomDelay_card` (`1 ≤ M ≤ 2^63`, `1 ≤ d ≤ M`): exactly `2 · ((2^63 − d)/M + 1)` draws give the delay `d`. With
  `2^63 = qM + r`, `0 ≤ r < M`: probability `(q+1)/2^63` for `d ≤ r` and `q/2^63` for `d > r`.
- `randomDelay_near_uniform` (same hypotheses): between `2⌊2^63/M⌋` and `2⌈2^63/M⌉` draws, a relative error of at most
  `M/2^63` against `1/M`. Uses `randomDelay_card`.
- `close_pair_prob` (`1 ≤ Mmin ≤ Mb ≤ 2^63`, `1 ≤ δ`; any offsets `a`, `b` and any first bound `Ma`): two timers fire
  less than `δ` apart with probability at most `(2δ − 1)⌈2^63/Mmin⌉/2^63`. Uses `randomDelay_range` and
  `randomDelay_near_uniform`.
- `contested_prob_le` (`1 ≤ n`, `1 ≤ δ`, `1 ≤ Mmin`, every bound in `[Mmin, 2^63]`): a round is contested with
  probability at most `contestedBound n δ Mmin`. Uses the same two.
- `all_contested_prob_le` (the same, for `K` rounds with causal offsets and bounds): all `K` rounds contested with
  probability at most `contestedBound n δ Mmin ^ K`. Uses `contested_prob_le`.
- `default_example`: `contestedBound 3 100 10000 < 6/100` and `contestedBound 3 100 10000 ^ 5 < 1/1000000`.

`close_pair_prob` is not used by the later proofs, which apply its counting core (the private `card_close_le`)
directly.

## Numbers

`contestedBound 3 100 10000 = 597 · 922337203685478 / 2^63 ≈ 0.0597` (exact computation with Python's `Fraction`).
Its powers bound `K` consecutive contested rounds:

| `K` | 1 | 2 | 3 | 4 | 5 | 10 |
|---|---|---|---|---|---|---|
| bound | 5.97% | 3.56e-3 | 2.13e-4 | 1.27e-5 | 7.58e-7 | 5.75e-13 |

Per round, for `δ = 100` ms and `Mmin = 10` s, the bound is `C(n,2) · 0.0199`: 1.99% for 2 candidates, 5.97% for 3,
11.9% for 4, 19.9% for 5, 89.6% for 10, and above 1 (saying nothing) from 11 candidates on. For 3 candidates and `Mmin = 10` s
it is above 1 from a margin of 1668 ms on.

`Mmin = 10000` presumes that every competing attempt has reached `max_timeout`; with the default settings that is attempt
99 (bounds 100 ms, 200 ms, …, 9.9 s before). For 3 candidates and `δ = 100` ms, the bound by attempt number of the
earliest competing attempt is: attempt 0 (bound 100 ms) 5.97, attempt 1 (200 ms) 2.99, attempt 5 (600 ms) 0.995,
attempt 10 (1.1 s) 0.543, attempt 20 (2.1 s) 0.284, attempt 50 (5.1 s) 0.117, attempt 99 (10 s) 0.0597. It is below 1
exactly when the smallest bound is at least 598 ms.

## Proof structure

All in `Sol_OpenSearchElectionTimer_all.lean`; private lemmas:

- `nonNegative_toLong`: `nonNegative (toLong x)` is `(2^63 − x) % 2^63` on the lower half of `Fin (2^64)` and
  `x − 2^63` on the upper half.
- `card_filter_nonNegative`: for any decidable property `P`, the draws with `P (nonNegative (toLong x))` are exactly
  twice the `w < 2^63` with `P w` (two bijections, `Finset.card_nbij'`).
- `card_mod_eq`: the `w < N` with `w % M + 1 = d` number `(N − d)/M + 1`.
- `ceil_div_anti`: `⌈N/b⌉` is antitone in `b ≥ 1`.
- `card_close_le`: for a fixed target `t`, at most `(2δ − 1) · 2⌈2^63/Mmin⌉` draws give a delay (bound in
  `[Mmin, 2^63]`) less than `δ` away from `t`: the open interval holds `2δ − 1` integers, each with at most
  `2⌈2^63/Mmin⌉` preimages.
- `sum_piSplitAt`, `piSplitAt_symm_self`, `piSplitAt_symm_ne`: a sum over `ι → A` split along one coordinate
  (`Equiv.piSplitAt`).
- `card_pairs_lt`: `C(n, 2)` pairs `i < j` in `Fin n`.
- `card_pair_close_le`: for `i ≠ j`, at most `(2^64)^(n−1) · (2δ − 1) · 2⌈2^63/Mmin⌉` draws make `i` and `j` fire
  less than `δ` apart (split off `j`'s draw, apply `card_close_le`).

`contested_prob_le` covers the contested draws by the union over pairs (the first candidate to fire and a close
follower) and applies `Finset.card_biUnion_le`. `all_contested_prob_le` is an induction over the rounds: with `S j` the
number of draws whose first `j` rounds are contested, `S (j+1) ≤ contestedBound · S j`, because, for fixed draws of the
other rounds, round `j`'s offsets and bounds and the event on the earlier rounds do not depend on round `j`'s draws
(`hcausal`), and `contested_prob_le` bounds round `j`. `default_example` is `unfold contestedBound` followed by
`norm_num [Nat.choose]`.

## Idealizations

- **Uniform 64-bit draws.** The model draws uniformly from all `2^64` longs. `java.util.Random` is a 48-bit linear
  congruential generator; `nextLong()` combines two 32-bit outputs and takes at most `2^48` of the `2^64` values. The
  theorems say nothing about the delays the actual generator produces; that its outputs reduced modulo `M ≤ 300000` are
  close to uniform is plausible but not proved here.
- **Independence.** Draws are independent across nodes and attempts. In Java a node's successive attempts use successive
  outputs of one generator (interleaved with the rare `nextInt` of an abdication), and the nodes' generators are seeded
  from `Randomness.get().nextLong()` (DiscoveryModule.java:213), about which nothing is modelled: correlated seeds would
  correlate the nodes' delays.
- **Rounds.** Grouping competing timers into rounds, each with given offsets and bounds, abstracts the scheduler's
  timeline. Every round has the same `n` candidates, each drawing afresh (a candidate that sits a round out can only be
  represented by a very large offset); the rounds need not be ordered in time, and nothing ties a round to the
  scheduler's attempt number. The model does not say what happens between rounds, or that a round ends. The adversary of
  `all_contested_prob_le` is a deterministic function of the earlier rounds' draws: it chooses offsets and bounds, not
  message delays or which candidates take part, and it cannot react to the current round's draws.
- **The union bound.** `contestedBound` is a union bound over pairs and is at least 1 for many candidates, a large
  margin `δ`, or small bounds (above); there the theorems hold trivially (a probability is at most 1), although their
  hypotheses are satisfiable.
- **Bounds up to `2^63`.** Every bound is at most `2^63`; the Java settings allow at most 300000 ms.

## How the missions connect

The chain is: timers, uncontested rounds, stable elections, publications.

- `OpenSearchPreVote` transcribes the scheduler (`maxDelay`, `nonNegative`, `toPositiveLongAtMost`, `attemptDelay`) and
  proves the deterministic facts: every delay lies in `[g + 1, g + maxDelay]` (`attemptDelay_bounds`), the bounds back off
  linearly to `max_timeout` (`maxDelay_schedule`), and `nonNegative` maps the longs two-to-one onto `[0, 2^63)`
  (`nonNegative_two_to_one`, the counting fact this mission reproves over `Fin (2^64)` as `card_filter_nonNegative`).
- This mission adds the probability: a round of competing timers whose bounds all lie in `[Mmin, 2^63]` is
  uncontested with margin `δ` except with probability at most `contestedBound n δ Mmin`, and `K` contested rounds have
  probability at most its `K`-th power.
- `OpenSearchProgress` proves that a stable election succeeds: with a quorum of voters no fresher than the candidate and
  in lower terms, in a period without competing start-join requests (of the candidate's term or higher), without new
  publications, without bootstraps or restarts of the candidate or the voters, and without publications fresher than
  the candidate's state accepted by them, the candidate wins once the voters' joins are counted, and such executions
  exist. The connection "an uncontested round with margin `δ` gives
  a stable election period" is informal: it needs the
  first candidate's pre-voting round and election to complete within `δ` (bounded message delays, healthy voters whose
  states are no fresher than the candidate's, no competing request from another source such as abdication), none of
  which is modelled here; once every node of a quorum of the last committed or of the last accepted configuration in a
  candidate's cluster state is unhealthy or knows a leader other than that candidate, the candidate's pre-voting rounds
  over that state start no election (`OpenSearchPreVote.no_disruption`, with the nodes' health and leader knowledge
  fixed while the round runs).

## Checks

- `lake env lean` (in `mathlib/`) on a copy of `Sol_OpenSearchElectionTimer_all.lean` with `#print axioms` for the seven
  theorems: no errors (about 11 s with the Mathlib cache); every theorem depends only on `propext`, `Classical.choice`
  and `Quot.sound`. The file contains no `sorry`, `native_decide`, `bv_decide` or custom syntax.
- The seven split files `Solutions/Sol_OpenSearchElectionTimer_<name>.lean` compile with `lake env lean` without any
  message; their only `sorry`s are the imported `Theorems/` stubs. Their `import Theorems.Thm_OpenSearchElectionTimer_...`
  lines agree with the in-file dependencies and with `ORDER` in the items file (file order): `randomDelay_near_uniform`
  imports `randomDelay_card`; `close_pair_prob`, `contested_prob_le` and `default_example` import
  `randomDelay_near_uniform` and `randomDelay_range` (each split file carries the preceding private lemmas, and
  `card_close_le` uses both; `default_example` does not need them); `all_contested_prob_le` imports those two and
  `contested_prob_le`.
- The numbers above were recomputed independently with exact rational arithmetic in Python.

## What is not proved

- **The actual generator.** Nothing about `java.util.Random`'s outputs, their reduction modulo the bound, or the
  correlation of seeds; the uniform 64-bit model is an assumption.
- **That an uncontested round yields a successful election.** The step from "one candidate fires `δ` before the others"
  to the stable election period of `OpenSearchProgress` is informal; nothing bounds how long a pre-voting round or an
  election takes.
- **Time to elect.** No bound on the expected time until a cluster-manager is elected, and no account of the attempts
  before the bounds reach `Mmin` (with the default settings the first 99 attempts have smaller bounds).
- **That real networks eventually become stable**, the scheduling of the candidates' timers by the `Coordinator` (when
  nodes become candidates, the `LeaderChecker` and `FollowersChecker` that trigger it), and failure detection in
  general.
