import Mathlib
import Definitions.Def_OpenSearchPreVote

/-!
# OpenSearch cluster coordination: randomized election timers

A cluster-manager-eligible node that has no leader schedules a pre-voting round after a random delay
(`ElectionSchedulerFactory`, OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java`, cited `ESF:<line>`):
attempt `k` fires `toPositiveLongAtMost(random.nextLong(), maxDelay k) + gracePeriod` milliseconds after it was
scheduled (ESF:201-204; the timer is scheduled at ESF:240), with `maxDelay` and `toPositiveLongAtMost` transcribed in
`Def_OpenSearchPreVote`. When two candidates run at nearly the same time they can split the votes and both fail. The
randomization aims to make one candidate's timer fire far enough ahead of every other's that it runs alone, its
pre-voting round and election completing before anyone else starts. That step is informal and not modelled here:
whether a firing starts a pre-voting round at all (only if the node is still a candidate that may win the election, is
healthy and is commissioned, `Coordinator.java:1579-1608`), and whether the round and the election complete within that
head start, depend on timing and state this file does not have. The progress mission (`OpenSearchProgress`) proves that
an election succeeds in a stable period, in its sense; that an uncontested round yields such a period is not proved.

This file models one round of competing timers. Candidate `i` fires at `offset i + randomDelay (bound i) (x i)`, where
`x i` is its draw of `random.nextLong()`; `bound i` stands for its attempt's `maxDelay` and `offset i` for when its
timer was started plus the grace period, a reading that no definition here formalizes: offsets and bounds are free
parameters. The probability theorems hold whatever the offsets and bounds, even chosen by an adversary that schedules
the network (as a function of the earlier rounds' draws), provided `n ≥ 1`, `δ ≥ 1`, `Mmin ≥ 1` and every bound lies in
`[Mmin, 2^63]` (`close_pair_prob` constrains only the second timer's bound). With `Mmin = cluster.election.max_timeout`
they apply once every competing attempt has reached that timeout, which with the default settings is from attempt 99
on, counting from 0. Probabilities are counts of draws divided by `2^(64 n)`.

Idealization: each node's scheduler draws from the node's `java.util.Random` (the Coordinator's, which also uses it to
pick a node to abdicate to, `Coordinator.java:1818`), seeded from `Randomness.get().nextLong()`
(`DiscoveryModule.java:213`); the draws are modelled as uniform over the `2^64` Java `long`s and independent across
nodes and attempts. `java.util.Random` is a 48-bit linear congruential generator, so `nextLong()` takes at most `2^48`
distinct values; the model does not capture that, nor any correlation between seeds. Grouping competing timers into
rounds is itself an abstraction of the scheduler's timeline.
-/

namespace OpenSearchElectionTimer

open OpenSearchPreVote

/-- A value of `random.nextLong()`: an element of `Fin (2^64)`, read as the Java `long` `x - 2^63`. -/
def toLong (x : Fin (2 ^ 64)) : Int := (x.val : Int) - 2 ^ 63

/-- The random part of the delay of an attempt with bound `M` for the draw `x`: `toPositiveLongAtMost(x, M)`
(ESF:204). -/
def randomDelay (M : Nat) (x : Fin (2 ^ 64)) : Nat := toPositiveLongAtMost (toLong x) M

/-- The time at which candidate `i` fires, given every candidate's offset, bound and draw. -/
def fireTime {n : Nat} (offset : Fin n → Int) (bound : Fin n → Nat) (x : Fin n → Fin (2 ^ 64)) (i : Fin n) : Int :=
  offset i + randomDelay (bound i) (x i)

/-- A round is *uncontested with margin `δ`*: some candidate fires at least `δ` before every other candidate. -/
def Uncontested {n : Nat} (offset : Fin n → Int) (bound : Fin n → Nat) (δ : Nat) (x : Fin n → Fin (2 ^ 64)) : Prop :=
  ∃ i, ∀ j, j ≠ i → fireTime offset bound x i + δ ≤ fireTime offset bound x j

instance {n : Nat} (offset : Fin n → Int) (bound : Fin n → Nat) (δ : Nat) :
    DecidablePred (Uncontested offset bound δ) := fun x => by
  unfold Uncontested; infer_instance

/-- The per-round bound on the probability of a contested round: `C(n,2) · (2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63` for `δ ≥ 1`
and `Mmin ≥ 1`. It is computed with natural-number subtraction and division, so it is 0 when `δ = 0` or `Mmin = 0`, and
it is not capped at 1. -/
def contestedBound (n δ Mmin : Nat) : ℚ :=
  (n.choose 2 : ℚ) * (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63

end OpenSearchElectionTimer
