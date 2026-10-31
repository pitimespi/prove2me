import Mathlib
import Definitions.Def_OpenSearchPreVote

/-!
# OpenSearch cluster coordination: randomized election timers

A cluster-manager-eligible node that has no leader schedules a pre-voting round after a random delay
(`ElectionSchedulerFactory`, OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`,
`server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java`, cited `ESF:<line>`):
attempt `k` fires `toPositiveLongAtMost(random.nextLong(), maxDelay k) + gracePeriod` milliseconds after it was
scheduled (ESF:195-204), with `maxDelay` and `toPositiveLongAtMost` transcribed in `Def_OpenSearchPreVote`. When two
candidates run at nearly the same time they can split the votes and both fail; when one candidate's timer fires
sufficiently earlier than every other's, it runs alone: its pre-voting round and election complete before anyone else
starts (the progress missions prove that such a stable election succeeds).

This file models one round of competing timers. Candidate `i` fires at `offset i + randomDelay (bound i) (x i)`, where
`x i` is its draw of `random.nextLong()` — modelled as uniform over the `2^64` Java `long`s, independently across
candidates and attempts — `bound i` is its attempt's `maxDelay`, and `offset i` (when its timer was started, plus the
grace period) is arbitrary: the theorems hold whatever the offsets and bounds, even chosen by an adversary that
schedules the network, provided every bound is at least some `Mmin` (they hold, for example, once every attempt has
reached `cluster.election.max_timeout`). Probabilities are counts of draws divided by `2^(64 n)`.
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

/-- The per-round bound on the probability of a contested round: `C(n,2) · (2δ - 1) · ⌈2^63 / Mmin⌉ / 2^63`. -/
def contestedBound (n δ Mmin : Nat) : ℚ :=
  (n.choose 2 : ℚ) * (2 * δ - 1 : ℕ) * ((2 ^ 63 + Mmin - 1) / Mmin : ℕ) / 2 ^ 63

end OpenSearchElectionTimer
