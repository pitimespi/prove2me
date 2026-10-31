# Read-back: `Def_OpenSearchElectionTimer.lean`

Sources read: `mathlib/Definitions/Def_OpenSearchElectionTimer.lean` and, for the imported definitions, `Definitions/Def_OpenSearchPreVote.lean` (the top-level copy, as directed; see the last section). The file imports all of Mathlib and `Definitions.Def_OpenSearchPreVote`. It opens the namespace `OpenSearchElectionTimer` (with `open OpenSearchPreVote`) and introduces, in order, five definitions and one instance: `toLong`, `randomDelay`, `fireTime`, `Uncontested`, an anonymous `DecidablePred` instance for `Uncontested`, and `contestedBound`. There are no structures, axioms, hypotheses or `sorry`s.

Notation used below: $\mathbb{N}$ (Lean `Nat`), $\mathbb{Z}$ (`Int`), $\mathbb{Q}$ (`ℚ`), $\mathrm{Fin}(m) = \{0, \dots, m-1\}$. $a \mathbin{\dot-} b$ is truncated natural-number subtraction ($= 0$ when $b \ge a$). $a \operatorname{div} b$ is natural-number floor division, with $a \operatorname{div} 0 = 0$. $a \bmod b$ is the natural-number remainder, with $a \bmod 0 = a$. These are Lean's conventions.

## Imported notions, expanded

Only two imported definitions occur in Lean terms of this file: `toPositiveLongAtMost`, used by `randomDelay`, and through it `nonNegative`.

**`nonNegative`** (imported). $\mathrm{nonNegative} : \mathbb{Z} \to \mathbb{N}$,
$$\mathrm{nonNegative}(n) = \begin{cases} 0 & \text{if } n = -2^{63},\\ |n| & \text{otherwise.}\end{cases}$$
Lean's `-2 ^ 63` means $-(2^{63})$, i.e. Java's `Long.MIN_VALUE`. The function is defined on every integer. On the Java `long` range $[-2^{63}, 2^{63}-1]$ its values lie in $[0, 2^{63}-1]$. Each value is taken exactly twice: $0$ by $n = -2^{63}$ and by $n = 0$, and each $v \in [1, 2^{63}-1]$ by $n = v$ and $n = -v$. (I derived this; the file does not state it.)

**`toPositiveLongAtMost`** (imported). $\mathrm{toPositiveLongAtMost} : \mathbb{Z} \times \mathbb{N} \to \mathbb{N}$,
$$\mathrm{toPositiveLongAtMost}(r, M) = (\mathrm{nonNegative}(r) \bmod M) + 1 .$$
For $M \ge 1$ the value lies in $[1, M]$. For $M = 0$ there is no guard, and the value is $\mathrm{nonNegative}(r) + 1$, because $a \bmod 0 = a$. The Java method instead asserts `0 < upperBound`, and `% 0` on a `long` throws. $M$ is an unbounded natural number, while Java's `upperBound` is a `long`, at most $2^{63}-1$.

**Scheduler notions (named in docstrings only).** The imported file also defines the following:

- `SchedulerSettings`: four natural-number fields `initialTimeout`, `backoffTime`, `maxTimeout`, `duration`.
- `SchedulerSettings.default` $= \langle 100, 100, 10000, 500\rangle$.
- `SchedulerSettings.Valid`: $1 \le \mathrm{initialTimeout} \le 10000$, $1 \le \mathrm{backoffTime} \le 60000$, $200 \le \mathrm{maxTimeout} \le 300000$, $\mathrm{initialTimeout} \le \mathrm{maxTimeout}$, and $1 \le \mathrm{duration} \le 300000$.
- $\mathrm{maxDelay}(s, k) = \min(s.\mathrm{maxTimeout},\ s.\mathrm{initialTimeout} + k \cdot s.\mathrm{backoffTime})$.
- $\mathrm{attemptDelay}(s, k, r, g) = \mathrm{toPositiveLongAtMost}(r, \mathrm{maxDelay}(s, k)) + g$.

No Lean term in this file, or in any of the seven theorem stubs, uses any of these. This file's docstrings mention `maxDelay` by name. So the relation between the parameters `bound`/`offset` below and the real scheduler is stated only in prose.

## Declaration 1: `toLong`

$\mathrm{toLong} : \mathrm{Fin}(2^{64}) \to \mathbb{Z}$, $\ \mathrm{toLong}(x) = x - 2^{63}$ (the value of $x$, cast to an integer, minus $2^{63}$).

- It is an order-preserving bijection from $\{0, \dots, 2^{64}-1\}$ onto the Java `long` range $\{-2^{63}, \dots, 2^{63}-1\}$:
  - $x = 0 \mapsto -2^{63}$;
  - $x = 2^{63} \mapsto 0$;
  - $x = 2^{64}-1 \mapsto 2^{63}-1$.
- It is an offset encoding, not the two's-complement reading of a 64-bit pattern. That reading would map $x \mapsto x$ for $x < 2^{63}$ and $x \mapsto x - 2^{64}$ otherwise.
- Both are bijections, so any count taken over all $x$ is the same under either reading.

The docstring ("an element of `Fin (2^64)`, read as the Java `long` `x - 2^63`") matches the code.

## Declaration 2: `randomDelay`

$\mathrm{randomDelay} : \mathbb{N} \times \mathrm{Fin}(2^{64}) \to \mathbb{N}$,
$$\mathrm{randomDelay}(M, x) = \mathrm{toPositiveLongAtMost}(\mathrm{toLong}(x), M) = \big(\mathrm{nonNegative}(x - 2^{63}) \bmod M\big) + 1 .$$

- For $M \ge 1$ the value is in $[1, M]$.
- For $M = 0$ the value is $\mathrm{nonNegative}(x - 2^{63}) + 1 \in [1, 2^{63}]$, a case Java excludes.
- $M$ has no upper bound. For $M > 2^{63}$ the reduction does nothing and the values lie in $[1, 2^{63}]$.

A derived fact, not stated in the file: as $x$ ranges over $\mathrm{Fin}(2^{64})$, $\mathrm{nonNegative}(\mathrm{toLong}(x))$ takes each value of $[0, 2^{63}-1]$ exactly twice. Hence, for $1 \le d \le M \le 2^{63}$, exactly $2((2^{63} - d) \operatorname{div} M + 1)$ draws give delay $d$; this is the theorem `randomDelay_card`.

The docstring ("`toPositiveLongAtMost(x, M)` (ESF:204)") matches, with $x$ read through `toLong`.

## Declaration 3: `fireTime`

**Arguments:**
- $n \in \mathbb{N}$ (implicit);
- $\mathrm{offset} : \mathrm{Fin}\,n \to \mathbb{Z}$;
- $\mathrm{bound} : \mathrm{Fin}\,n \to \mathbb{N}$;
- $x : \mathrm{Fin}\,n \to \mathrm{Fin}(2^{64})$;
- $i \in \mathrm{Fin}\,n$.

**Definition:**
$$\mathrm{fireTime}(\mathrm{offset}, \mathrm{bound}, x, i) = \mathrm{offset}(i) + \mathrm{randomDelay}(\mathrm{bound}(i), x(i)) \in \mathbb{Z},$$
with the natural number cast to an integer. Below, $T_i$ denotes this value.

- $T_i$ depends only on $\mathrm{offset}(i)$, $\mathrm{bound}(i)$ and $x(i)$.
- The offsets are unconstrained (any integers, including negative ones), and so are the bounds (any naturals, including $0$).
- The code fixes no unit; the docstrings speak of milliseconds.

The docstring ("the time at which candidate `i` fires, given every candidate's offset, bound and draw") matches.

## Declaration 4: `Uncontested`

For $n$, $\mathrm{offset}$ and $\mathrm{bound}$ as above, $\delta \in \mathbb{N}$, and $x : \mathrm{Fin}\,n \to \mathrm{Fin}(2^{64})$:
$$\mathrm{Uncontested}(\mathrm{offset}, \mathrm{bound}, \delta, x) \iff \exists i \in \mathrm{Fin}\,n,\ \forall j \in \mathrm{Fin}\,n,\ j \ne i \Rightarrow T_i + \delta \le T_j,$$
computed in $\mathbb{Z}$ with $\delta$ cast to an integer. Cases:

- **$n = 0$:** false, because there is no $i$.
- **$n = 1$:** true for every $x$, because the inner quantifier is vacuous.
- **$\delta = 0$, $n \ge 1$:** true for every $x$, because any minimizer of $T$ is a witness.
- **$\delta \ge 1$, $n \ge 2$:** true exactly when one candidate has the strictly smallest fire time and the second-smallest fire time is at least $\min_i T_i + \delta$. The witness is then unique: two witnesses $i \ne i'$ would give $2\delta \le 0$.
  - Equivalently, for $\delta \ge 1$ and $n \ge 1$, "contested" ($\neg\mathrm{Uncontested}$) holds iff $n \ge 2$ and the two smallest fire times, counted with multiplicity, differ by less than $\delta$. Ties count as contested.

The docstring ("some candidate fires at least `δ` before every other candidate") matches. Nothing in the definition relates $\delta$ to message latency, the length of a pre-voting round, or the length of an election.

## Instance: `DecidablePred (Uncontested offset bound δ)`

Decidability is obtained by unfolding the definition and calling `infer_instance`: the quantifiers range over the finite type $\mathrm{Fin}\,n$, and $\le$ on $\mathbb{Z}$ is decidable. The instance only lets `Finset.filter` be applied to `Uncontested` in the theorem statements. It adds no meaning: membership in a filtered finset does not depend on which decidability instance is used.

## Declaration 5: `contestedBound`

$\mathrm{contestedBound} : \mathbb{N} \times \mathbb{N} \times \mathbb{N} \to \mathbb{Q}$,
$$\mathrm{contestedBound}(n, \delta, M_{\min}) = \frac{\binom{n}{2} \cdot (2\delta \mathbin{\dot-} 1) \cdot \big((2^{63} + M_{\min}) \mathbin{\dot-} 1\big) \operatorname{div} M_{\min}}{2^{63}} .$$
The three factors are computed in $\mathbb{N}$ and cast to $\mathbb{Q}$, and the division by $2^{63}$ is in $\mathbb{Q}$. `2 ^ 63 + Mmin - 1` associates as `(2^63 + Mmin) - 1`. Cases:

- **$\delta \ge 1$, $M_{\min} \ge 1$:** the value is $\binom{n}{2}(2\delta-1)\lceil 2^{63}/M_{\min}\rceil / 2^{63}$, the docstring's formula. Numerically it is $\binom{n}{2}(2\delta-1)/M_{\min}$, with a relative excess below $M_{\min}/2^{63}$.
- **$n \le 1$:** $0$, since $\binom{n}{2} = 0$.
- **$\delta = 0$:** $0$, by truncated subtraction. The docstring's $2\delta - 1$ would be $-1$.
- **$M_{\min} = 0$:** $0$, since Lean's division by zero gives $0$. The docstring's $\lceil 2^{63}/0\rceil$ is undefined.
- **Not capped at $1$:** for example, $\mathrm{contestedBound}(3, 100, M_{\min}) \ge 1$ exactly when $1 \le M_{\min} \le 597$. For such parameters, a theorem that uses it as an upper bound on a probability is trivially true.

The docstring calls this "the per-round bound on the probability of a contested round". The definition itself is only this number; its role as a bound is the content of `contested_prob_le`.

## Citation check against the Java source

The local checkout `/home/user/opensearch-project/OpenSearch` is at commit `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, the cited commit.

- **ESF:195-204** (`ElectionScheduler.scheduleNextElection`):
  - line 201: `thisAttempt = attempt.getAndIncrement()`, so attempts are numbered from 0;
  - line 203: `maxDelayMillis = Math.min(maxTimeout.millis(), initialTimeout.millis() + thisAttempt * backoffTime.millis())`;
  - line 204: `delayMillis = toPositiveLongAtMost(random.nextLong(), maxDelayMillis) + gracePeriod.millis()`.

  This matches the module docstring's formula and the `randomDelay` docstring (ESF:204). The scheduling call itself, `threadPool.scheduleUnlessShuttingDown(TimeValue.timeValueMillis(delayMillis), ...)`, is at ESF:240, outside the cited range.
- **ESF:159-161** (`nonNegative`): `n == Long.MIN_VALUE ? 0 : Math.abs(n)`. This matches the imported definition on the `long` range.
- **ESF:169-172** (`toPositiveLongAtMost`): `assert 0 < upperBound`, then `nonNegative(randomNumber) % upperBound + 1`. This matches for `upperBound` $\ge 1$. Java's `%` with a non-negative left operand and a positive right operand is the natural-number remainder. The Lean version has no counterpart of the assertion (see above).
- **DiscoveryModule.java:213**: `new Random(Randomness.get().nextLong())`, passed to the Coordinator as its `random`. Coordinator.java:263 passes it on as `new ElectionSchedulerFactory(settings, random, ...)`.
  - The same `Random` object is also used at Coordinator.java:1818 (`random.nextInt(...)`, which picks an abdication target). So the docstring's "each node's scheduler draws from its own `java.util.Random`" is slightly imprecise: the generator is the Coordinator's.
  - This does not matter under the stated idealization of independent uniform draws.
- **What a firing leads to.** When the timer runs (`doRun`, ESF:213-221), it does nothing if the scheduler has been closed. Otherwise it first schedules the next attempt, with grace period `duration` (ESF:218), and then runs the Coordinator's runnable (CO:1577-1610). That runnable starts a pre-voting round only if the node is in CANDIDATE mode, may win the election, is healthy, and is commissioned. The file models only fire times. The first attempt's grace period is `TimeValue.ZERO` (CO:1574); CO:1575 is the only call of `startElectionScheduler` on the factory.
- **"Uniform" in the Java comment.** The comment at ESF:71-83 says the delay is "chosen uniformly from (0, min(...)]". The transcribed modular reduction is uniform only under the 64-bit idealization, and even then only up to the rounding quantified by `randomDelay_card` and `randomDelay_near_uniform`: it is exactly uniform iff $M$ divides $2^{63}$.

## Docstring claims not carried by the Lean terms

1. "`bound i` is its attempt's `maxDelay`", and "`offset i` (when its timer was started, plus the grace period)". No Lean term links `bound` or `offset` to `maxDelay`, `SchedulerSettings`, or a grace period. They are free parameters.
2. "The theorems hold whatever the offsets and bounds … provided every bound is at least some `Mmin`." The theorem stubs also require:
   - every bound $\le 2^{63}$;
   - $n \ge 1$, $\delta \ge 1$ and $M_{\min} \ge 1$.

   `close_pair_prob` constrains only one of its two bounds.
3. "(They hold, for example, once every attempt has reached `cluster.election.max_timeout`.)" This is true as a choice of $M_{\min}$. Note, though, that with `SchedulerSettings.default`, $\mathrm{maxDelay}(\mathrm{default}, k) = \min(10000,\ 100 + 100k)$ reaches $10000$ only for $k \ge 99$, i.e. from the 100th attempt on.
4. "When one candidate's timer fires sufficiently earlier than every other's, it runs alone: its pre-voting round and election complete before anyone else starts (the progress missions prove that such a stable election succeeds)." Nothing in this file formalizes this. `Uncontested` concerns fire times only, and $\delta$ is a free parameter.
5. "Probabilities are counts of draws divided by `2^(64 n)`." This matches the stubs' denominators: $(2^{64})^2$, $(2^{64})^n$ and $(2^{64})^{nK}$.
6. The idealization paragraph is consistent with the code. Draws are elements of $\mathrm{Fin}(2^{64})$, and independence appears as counting over product types. The paragraph itself acknowledges that the real generator produces only $2^{48}$ distinct `nextLong()` values.
7. "This file models one round of competing timers." This is true of the definitions. The multi-round structure exists only in the stub `all_contested_prob_le`, whose `hcausal` hypothesis matches "as a function of the earlier rounds' draws".

## Note on the imported file

As instructed, I read `/home/user/prove2me/Definitions/Def_OpenSearchPreVote.lean`. This file and the theorem stubs live under `mathlib/`. A second copy, `mathlib/Definitions/Def_OpenSearchPreVote.lean`, exists there and is presumably what the import resolves to. I did not read that copy's content. A `diff` printing only line numbers shows that the two copies differ only in lines 141–145 (141–144 in the `mathlib/` copy). In the copy I read, those lines are the docstring of `handleJoins`, not any definition used here. `Def_OpenSearchPreVote` itself imports `Def_OpenSearchCoordination`, which I did not read. The two definitions used here, `nonNegative` and `toPositiveLongAtMost`, do not depend on it.
