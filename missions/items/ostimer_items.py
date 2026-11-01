SRC = ("OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, "
       "constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 "
       "and the next attempt scheduled with the election duration as grace period at 218): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; "
       "Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, "
       "startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; "
       "DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): "
       "https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; "
       "java.util.Random (a 48-bit linear congruential generator; nextLong): "
       "https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; "
       "maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission")
TAGS = ["opensearch", "elasticsearch", "consensus", "cluster-coordination", "leader-election", "election-scheduler",
        "randomized-timeout", "liveness", "probability", "union-bound", "formal-verification", "mathlib"]

DEFINITION = {
    "definition_name": "OpenSearchElectionTimer",
    "definition_title": "OpenSearch's randomized election timers: the random delay of an attempt, the firing times of competing candidates, uncontested rounds, and the per-round bound",
    "natural_language_statement": r"""A model of one round of competing randomized election timers of OpenSearch's `ElectionSchedulerFactory` at revision `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, over the scheduler functions transcribed by the `OpenSearchPreVote` mission (`nonNegative`, `toPositiveLongAtMost`), with Mathlib. In Java, a cluster-manager-eligible candidate's scheduler fires attempt `k` after `toPositiveLongAtMost(random.nextLong(), maxDelay) + gracePeriod` milliseconds (`ElectionSchedulerFactory.java:203-204`), where `maxDelay = min(max_timeout, initial_timeout + k · back_off_time)`, `toPositiveLongAtMost(r, M) = nonNegative(r) mod M + 1`, and the grace period is 0 for the first attempt and `cluster.election.duration` for the later ones; when an attempt fires it schedules the next one and, if the node is still a candidate that may win the election, is healthy and is commissioned, starts a new pre-voting round, closing the previous one (`Coordinator.java:1578-1608`).

**`toLong x`** — for `x : Fin (2^64)`, the integer `x − 2^63`: the `2^64` possible values of `random.nextLong()` are the elements of `Fin (2^64)`, read as Java `long`s. **`randomDelay M x`** — `toPositiveLongAtMost (toLong x) M`, the random part of the delay of an attempt with bound `M` for the draw `x`. For `M = 0`, which Java rules out (`assert 0 < upperBound`), the Lean value is `nonNegative (toLong x) + 1`. **`fireTime offset bound x i`** — for `n` candidates `i : Fin n`, offsets `offset : Fin n → ℤ`, bounds `bound : Fin n → ℕ` and draws `x : Fin n → Fin (2^64)`: `offset i + randomDelay (bound i) (x i)`, the time at which candidate `i` fires; `offset i` stands for the time its timer was started plus its grace period, and `bound i` for its attempt's `maxDelay`, but only informally: no Lean term links `offset` or `bound` to `maxDelay`, `SchedulerSettings` or a grace period, and the theorems quantify over them as free parameters. **`Uncontested offset bound δ x`** — the round is uncontested with margin `δ : ℕ`: some candidate `i` fires at least `δ` before every other, `fireTime offset bound x i + δ ≤ fireTime offset bound x j` for every `j ≠ i` (a decidable predicate). **`contestedBound n δ Mmin`** — the rational number `C(n, 2) · (2δ − 1) · ⌈2^63 / Mmin⌉ / 2^63`, where `2δ − 1` is computed in the natural numbers and `⌈2^63 / Mmin⌉` is written as the natural-number quotient `(2^63 + Mmin − 1) / Mmin`, which is the ceiling when `Mmin ≥ 1`. The value is 0 when `n ≤ 1`, `δ = 0` or `Mmin = 0`, and it is not capped at 1.

Probabilities are counts: a draw of the `n` candidates of a round is a function `Fin n → Fin (2^64)`, and the probability of a set of draws is its number of elements divided by `(2^64)^n`, which is the uniform distribution with independent candidates; over `K` rounds a draw is a function `Fin K → Fin n → Fin (2^64)` and the denominator is `(2^64)^(n K)`.

**Formalization Note.** The draws are idealized. Each node's scheduler draws from the node's own `java.util.Random`, created as `new Random(Randomness.get().nextLong())` (`DiscoveryModule.java:213`) and also used by the `Coordinator` to pick a node to abdicate to (`Coordinator.java:1818`); the model treats every draw as uniform over the `2^64` longs and independent of every other draw, across nodes and attempts. `java.util.Random` is a 48-bit linear congruential generator, so `nextLong()` takes at most `2^48` of the `2^64` values, and the successive draws of one node are successive outputs of one generator; neither this nor any correlation between the seeds of different nodes is modelled. Grouping competing timers into rounds is an abstraction of the scheduler's timeline. Within a round the offsets and bounds are arbitrary integers and naturals (the theorems require every bound to lie in `[Mmin, 2^63]`); across rounds they may be any deterministic function of the earlier rounds' draws, never of the current round's. Every round has the same `n` candidates, each drawing afresh (a candidate that sits a round out can only be represented by a very large offset); the rounds need not be ordered in time, and nothing ties a round to the scheduler's attempt number. What happens between rounds is not modelled, nor whether an uncontested round leads to a successful election. Imports Mathlib and the `OpenSearchPreVote` definitions.""",
}

THEOREMS = {
"OpenSearchElectionTimer.randomDelay_range": dict(
    title="Every random delay lies between one millisecond and the bound",
    nl=r"""For every natural number `M` with `1 ≤ M` and every draw `x : Fin (2^64)`: `1 ≤ randomDelay M x` and `randomDelay M x ≤ M`. The random part of an attempt's delay lies in `(0, M]`, the range stated by the scheduler's documentation (`ElectionSchedulerFactory.java:71-83, 163-167`).""",
    ms=None),
"OpenSearchElectionTimer.randomDelay_card": dict(
    title="The exact distribution of a random delay",
    nl=r"""For all natural numbers `M` and `d` with `1 ≤ M ≤ 2^63` and `1 ≤ d ≤ M`: the number of draws `x : Fin (2^64)` with `randomDelay M x = d` is exactly `2 · (⌊(2^63 − d) / M⌋ + 1)`.

Equivalently, writing `2^63 = qM + r` with `0 ≤ r < M`, each of the delays `1, …, r` has probability `(q + 1) / 2^63` and each of the delays `r + 1, …, M` has probability `q / 2^63`, for a draw uniform over the `2^64` longs: `nonNegative` maps the longs two-to-one onto `[0, 2^63)`, and the residues modulo `M` of `[0, 2^63)` occur `q + 1` or `q` times. The distribution is uniform exactly when `M` divides `2^63`.""",
    ms=("The exact distribution of a delay", "nonNegative ∘ toLong is two-to-one onto [0, 2^63), one bijection for each half of the longs; the w < 2^63 with w mod M = d − 1 are the d − 1 + kM with k ≤ (2^63 − d)/M.")),
"OpenSearchElectionTimer.randomDelay_near_uniform": dict(
    title="Random delays are uniform up to a relative error of M / 2^63",
    nl=r"""For all natural numbers `M` and `d` with `1 ≤ M ≤ 2^63` and `1 ≤ d ≤ M`: `2 · ⌊2^63 / M⌋ ≤ #{x : Fin (2^64) | randomDelay M x = d} ≤ 2 · ⌈2^63 / M⌉`, the ceiling being written `(2^63 + M − 1) / M`.

For a uniform draw, each delay `d ∈ [1, M]` has a probability between `⌊2^63 / M⌋ / 2^63` and `⌈2^63 / M⌉ / 2^63`, that is, within a factor `1 ± M / 2^63` of `1 / M`. For the default maximum timeout `M = 10000` milliseconds, `M / 2^63` is about `1.1 · 10^-15`.""",
    ms=None),
"OpenSearchElectionTimer.close_pair_prob": dict(
    title="Two timers fire less than δ apart with probability at most about (2δ − 1)/Mmin",
    nl=r"""For all integers `a`, `b` and natural numbers `Ma`, `Mb`, `Mmin`, `δ` with `1 ≤ Mmin`, `Mmin ≤ Mb ≤ 2^63` and `1 ≤ δ`: the number of pairs of draws `(x, y) : Fin (2^64) × Fin (2^64)` with `|(a + randomDelay Ma x) − (b + randomDelay Mb y)| < δ`, divided by `(2^64)^2`, is at most `(2δ − 1) · ⌈2^63 / Mmin⌉ / 2^63`, where `2δ − 1` is computed in the natural numbers and `⌈2^63 / Mmin⌉ = (2^63 + Mmin − 1) / Mmin`.

Two candidates with offsets `a` and `b` and independent uniform draws fire less than `δ` milliseconds apart with probability at most about `(2δ − 1) / Mmin`, whatever the offsets and whatever the first candidate's bound `Ma`, on which nothing is assumed: for each value of the first draw, the second delay must fall among the `2δ − 1` integers less than `δ` away from a fixed point. With `δ = 100` and `Mmin = 10000` the bound is about 1.99%.""",
    ms=("The two-timer bound", "Fix the first draw: the second delay must lie in an open interval containing 2δ − 1 integers, and each value has at most 2⌈2^63/Mmin⌉ preimages.")),
"OpenSearchElectionTimer.contested_prob_le": dict(
    title="A round of competing timers is contested with probability at most contestedBound n δ Mmin",
    nl=r"""For all natural numbers `n`, `δ`, `Mmin` with `1 ≤ n`, `1 ≤ δ` and `1 ≤ Mmin`, every `offset : Fin n → ℤ` and every `bound : Fin n → ℕ` with `Mmin ≤ bound i ≤ 2^63` for every `i`: the number of draws `x : Fin n → Fin (2^64)` with `¬ Uncontested offset bound δ x`, divided by `(2^64)^n`, is at most `contestedBound n δ Mmin = C(n, 2) · (2δ − 1) · ⌈2^63 / Mmin⌉ / 2^63`.

Among `n` candidates with arbitrary offsets and bounds at least `Mmin`, the probability that no candidate fires at least `δ` before all the others is at most about `C(n, 2) · (2δ − 1) / Mmin`. In a contested round the first candidate to fire has a follower less than `δ` behind it, and the bound is `C(n, 2)` times that of `close_pair_prob`, a union bound over the pairs. It exceeds 1, and then says nothing, when `C(n, 2) · (2δ − 1)` exceeds about `Mmin`: for `δ = 100` and `Mmin = 10000`, from `n = 11` candidates on.""",
    ms=("The per-round bound", "A contested round contains a pair of candidates firing less than δ apart; a union bound over the C(n, 2) pairs, each pair bounded by fixing every draw but one.")),
"OpenSearchElectionTimer.all_contested_prob_le": dict(
    title="Repeated contests become exponentially unlikely once the per-round bound is below 1, even against an adaptive scheduler",
    nl=r"""For all natural numbers `n`, `K`, `δ`, `Mmin` with `1 ≤ n`, `1 ≤ δ` and `1 ≤ Mmin`, and all functions `offset : Fin K → (Fin K → Fin n → Fin (2^64)) → Fin n → ℤ` and `bound : Fin K → (Fin K → Fin n → Fin (2^64)) → Fin n → ℕ` (the offsets and bounds of round `k` for candidate `i`, given the draw `X` of all `K` rounds) such that

- every bound lies between `Mmin` and `2^63`: `Mmin ≤ bound k X i ≤ 2^63` for all `k`, `X` and `i`;
- the offsets and bounds of round `k` depend only on the draws of the earlier rounds: for all `k`, `X` and `X'`, if `X m = X' m` for every `m < k`, then `offset k X = offset k X'` and `bound k X = bound k X'`;

the number of draws `X : Fin K → Fin n → Fin (2^64)` such that every round is contested, `¬ Uncontested (offset k X) (bound k X) δ (X k)` for every `k : Fin K`, divided by `(2^64)^(n K)`, is at most `contestedBound n δ Mmin ^ K`.

An adversary that schedules the network, choosing deterministically when each candidate's timer of round `k` starts and with which bound, in reaction to everything drawn in the earlier rounds but not to the draws of round `k` or later, cannot make `K` rounds of the same `n` candidates (each drawing afresh in every round) all contested with probability above `contestedBound n δ Mmin ^ K`. That bound decreases exponentially in `K` when `contestedBound n δ Mmin < 1` and says nothing otherwise.""",
    ms=None),
"OpenSearchElectionTimer.default_example": dict(
    title="The default maximum timeout: three candidates, every bound at 10 s, and a 100 ms margin",
    nl=r"""`contestedBound 3 100 10000 < 6 / 100` and `contestedBound 3 100 10000 ^ 5 < 1 / 1000000`.

With every bound at OpenSearch's default `cluster.election.max_timeout` of 10 seconds (`Mmin = 10000` milliseconds; with the default initial timeout and back-off time of 100 ms, every attempt from attempt 99 on, counting from 0, has reached it), three competing candidates and a margin of `δ = 100` milliseconds, `contested_prob_le` bounds the probability of a contested round by `contestedBound 3 100 10000 = 597 · 922337203685478 / 2^63 ≈ 0.0597`, below 6%, and `all_contested_prob_le` bounds the probability that five consecutive rounds are contested by its fifth power, about `7.6 · 10^-7`, below one in a million. The theorem itself is arithmetic on these literals. The margin of 100 ms is an illustrative choice: nothing in the model shows that it suffices for a pre-voting round and an election to complete. For earlier attempts, whose bounds are smaller, the bound is weaker: for three candidates and a 100 ms margin it is at least 1, saying nothing, whenever the smallest competing bound is at most 597 ms.""",
    ms=("The default maximum timeout", "Evaluate the bound for three candidates, a 10 s bound and a 100 ms margin: under 6%, and its fifth power under one in a million.")),
}
ORDER = ["OpenSearchElectionTimer." + k for k in ["randomDelay_range", "randomDelay_card", "randomDelay_near_uniform",
  "close_pair_prob", "contested_prob_le", "all_contested_prob_le", "default_example"]]
