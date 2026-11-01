# OpenSearch cluster coordination: progress under stability (`OpenSearchProgress`)

Mission over OpenSearch `b2a54ba5c0defba3d1d20423e911d4bf920bab19`, built on the cluster model and the inductive
invariant of the safety mission (`OpenSearchSafety`, see `NOTES_OpenSearchSafety.md`), itself over the per-node
transcription of `CoordinationState` (`NOTES_OpenSearchCoordination.md`). 6 theorems, all proved.

- Stable periods: `Definitions/Def_OpenSearchProgress.lean` (imports `Def_OpenSearchSafety`, nothing else).
- Proofs: `Solutions/Sol_OpenSearchProgress_all.lean`; the 6 split files `Solutions/Sol_OpenSearchProgress_<name>.lean` and
  the statement stubs `Theorems/Thm_OpenSearchProgress_<name>.lean`. The proofs use four safety theorems through their
  stubs: `reachable_inv`, `inv_descends_parent`, `inv_descends_key`, `inv_eligible_of_won`.
- Prose: `missions/items/osprogress_items.py`, `missions/descriptions/osprogress_description.md`,
  `missions/explanations/expl_OpenSearchProgress_*.md` (one per theorem).
- Goal theorem: `OpenSearchProgress.election_possible` (from any cluster satisfying the election hypotheses, some stable
  election execution ends with the candidate elected), as in `README.md` and `STATUS.md`; the items leave no milestone
  on it.

Citations: `CO` Coordinator.java, `CS` CoordinationState.java (both in
`server/src/main/java/org/opensearch/cluster/coordination/`), with line numbers at the pinned revision. FLP is Fischer,
Lynch, Paterson, *Impossibility of distributed consensus with one faulty process* (J. ACM 1985); DLS is Dwork, Lynch,
Stockmeyer, *Consensus in the presence of partial synchrony* (J. ACM 1988).

## Why a stable period

Safety holds in every execution of the safety model. Progress cannot: a message may never be delivered, and competing
candidates can keep starting elections in higher terms, each start-join discarding the votes and the leadership of the
term before. FLP shows that no deterministic consensus protocol guarantees termination in an asynchronous network with
one crash failure; Paxos- and Raft-like protocols are safe always and live under partial synchrony (DLS), when the
network behaves well for long enough. OpenSearch makes such periods likely with pre-voting and randomized election
timers. The theorems therefore quantify over the executions of a *stable period*, defined by the steps it excludes, and
make three kinds of statement about them, under the hypotheses tabulated below: in every such execution, three handler
calls the protocol needs succeed (the candidate's `handleJoin` of a voter's join for `t`, once the candidate is in term
`t`, counting the vote; `handlePublishRequest` of the publication at a node of `Q` in term `t` that has not already
acknowledged it; the cluster-manager's `handlePublishResponse` of an acknowledgement sent to it by a node of `Q`,
counting it); once all of a quorum's votes (acknowledgements) are counted, the election is won (the publication
committed), whatever else happened; and such executions exist. No theorem states that the start-joins an election or a
publication needs stay enabled (the periods allow them, and `handleStartJoin` checks only the term), and the
publication statement does not cover nodes of `Q` outside term `t`.

## The model

### Stable steps

`ElectionStep P c t Q kt kv` and `PublicationStep P c t Q` restate the nine constructors of the safety model's
`Step P` with the same hypotheses and effects, adding a condition to some of them (and dropping `clientValue` from the
election period). `(kt, kv)` stands for the term and version of the candidate's accepted state when the election period
starts; the theorems instantiate them with `(W.node c).lastAcceptedTerm` and `(W.node c).lastAcceptedVersion`. The
bound compares a publication's version, while `hfresh` and `handleJoin` compare versions-or-metadata-versions; the two
agree wherever the bound matters, because every publication has term at least 1 (`pub_wf`): if `kt = 0` the bound
admits no publication, and otherwise the candidate's accepted state and every publication a voter accepts have term at
least 1, where the version-or-metadata-version is the version (`vomv_pos`). "Any" means: as in `Step`.

| step of `Step` | stable election for `c`, `t`, `Q`, `(kt, kv)` | stable publication for `c`, `t`, `Q` |
|---|---|---|
| `bootstrap` at `n` | `n ≠ c` and `n ∉ Q` | any |
| `startJoin` at `n`, request from eligible `src` for `t'` | `t' < t`, or `src = c` and `t' = t` | `t' ≤ t` if `n = c` or `n ∈ Q` |
| `join` | any | any |
| `clientValue` at `n` | never | `n ≠ c` |
| `publish` at `n` of a sent state `s` | if `n = c` or `n ∈ Q`: `s.term < kt`, or `s.term = kt` and `s.version ≤ kv` | any |
| `respond` | any | any |
| `commit` | any | any |
| `restart` of an eligible `n` | `n ≠ c` and `n ∉ Q` | `n ≠ c` |
| `restartAny` of a non-eligible `n` | any | any |

`ElectionExec` and `PublicationExec` are the reflexive-transitive closures: finite sequences of stable steps. Every
stable step is a `Step` (private `estep_step`, `pstep_step`), so a stable execution from a reachable cluster stays
reachable (`eexec_reach`, `pexec_reach`) and `reachable_inv` gives the safety invariant at every cluster along it.
Messages are still never removed: within the period a message may be handled any number of times, in any order, or
never.

### What each restriction protects

The docstrings of the two relations state what is excluded; the notes below say what each exclusion protects in the
proofs.

- **Election: start-join requests in terms at least `t`, other than `c`'s own for `t`.** A voter that handled one
  would no longer be below `t` when `c`'s request arrives, and `c` itself would move past `t`, or reach `t` by voting
  for another candidate. Requests of lower terms are allowed everywhere: a voter stays below `t`, and a join for a lower
  term is not a vote in term `t`.
- **Election: no new publication.** The period is one in which no node runs `handleClientValue`; the inductions over
  an election period have no such case.
- **Election: no bootstrap or restart of `c` or of a voter.** A restart replaces the transient state by the
  constructor's, clearing `c`'s started-join flag and votes. A restart or a bootstrap may rebuild a voter's metadata
  version (`RestartState` keeps term, version, configurations and UUID flags only; `initialStateContract` does not fix
  the metadata version), which the join of a term-0 state carries, and so make its join fresher than `c`'s state.
- **Election: no acceptance by `c` or a voter of a publication fresher than `(kt, kv)`.** This is the stale publication
  of a former cluster-manager arriving during the election: a voter that accepted it would send a join that
  `handleJoin` rejects as fresher than `c`'s state. At `c` the condition excludes every acceptance, since
  `handlePublishRequest` accepts only states fresher than the node's own (publications have term at least 1, so the
  Zen1 branch is dead, `pub_wf`): `c`'s accepted term, version and configurations stay fixed up to a commit.
- **Publication: start-join requests above `t` at `c` or a node of `Q`.** `c` would leave term `t` and its election; a
  node of `Q` in a higher term rejects the publication. Requests of terms at most `t` fail at `c` and let a node of `Q`
  reach term `t`, as `Coordinator.ensureTermAtLeast` does when a node receives a publication of a higher term (CO:512,
  635-641).
- **Publication: no further publication by `c`.** `handlePublishResponse` counts only acknowledgements of the last
  published version; a new publication would need a period of its own.
- **Publication: no restart of `c`.** A restart clears `electionWon` and the publish votes.

Notably allowed: commits at `c` in both periods (in the publication period this is the D1 behaviour, below); restarts of
the nodes of `Q` during a publication (an eligible node keeps its current term, its accepted state's term and, unless it
never joined a cluster, its version, `RestartState`; acknowledgements already sent stay sent); duplicate deliveries,
which the witness of `publication_possible` uses.

## Hypotheses

Common to all six theorems: payload type `V`, `P.InitCompatible`, `P.strategy = ElectionStrategy.DEFAULT_INSTANCE`,
`Reachable P W` for the cluster `W` at which the period starts, and the members of `Q` cluster-manager-eligible.

| | `election_vote_accepted` | `election_won` | `election_possible` |
|---|---|---|---|
| `c` eligible | yes | yes | yes |
| `c` and `Q` in terms below `t` at `W` | yes | yes | yes |
| each voter no fresher than `c` (`lastAcceptedTerm`, then `lastAcceptedVersionOrMetadataVersion`, as `handleJoin` compares) | yes | no | yes |
| `c`'s last accepted configuration nonempty | yes | implied by the quorum | implied by the quorum |
| `Q` a quorum of `c`'s last committed and last accepted configurations at `W` | no | yes | yes |
| at the end `W'` of the stable execution | `c` in term `t`; a sent join for `t` from a voter to `c` | `c` in term `t`; all of `Q` in `c`'s join votes | (existential) |

| | `publication_acks_accepted` | `publication_committed` | `publication_possible` |
|---|---|---|---|
| `c` elected and in term `t` at `W`; `W.sent (.publishRequest c s pt pv)`, `s.term = t`, `s.version = (W.node c).lastPublishedVersion` | yes | yes | yes |
| `Q` a quorum of `c`'s two configurations and of `s`'s two | no | yes | yes |
| `(W.node c).publishVotes.nodes = []` | no | yes | no |
| the nodes of `Q` in terms at most `t` at `W` | no | no | yes |
| at the end `W'` | any | all of `Q` in `c`'s publish votes | (existential) |

No hypothesis says that `c` is eligible in the publication theorems: a publisher is (`pub_wf`). The proofs do not use
`hQ` and `hct` in `election_won`, nor `hQ` in `publication_committed`; there the eligibility of the members of `Q` is
already implied by their membership in a vote collection.

## Public theorems

- `election_vote_accepted`: in every stable election execution, once `c` is in term `t`, every sent join for `t` from a
  voter to `c` is accepted by `c`'s `handleJoin` and its source counted.
- `election_won`: in every stable election execution, once `c` is in term `t` with all of `Q` among its join votes,
  `electionWon` holds.
- `election_possible` (goal): some stable election execution ends with `c` in term `t` and elected.
- `publication_acks_accepted`: in every stable publication execution, every node of `Q` in term `t` has sent its
  acknowledgement of `(t, s.version)` to `c` or accepts `s` now, and `c` accepts and counts every such acknowledgement
  that has been sent.
- `publication_committed`: with the four quorums and no acknowledgement counted at the start, in every stable
  publication execution in which all of `Q` is counted, `Committed W' t s.version`.
- `publication_possible`: with the four quorums and `Q` in terms at most `t`, some stable publication execution ends
  with `Committed W' t s.version`.

## The four configurations of `publication_committed`

`handlePublishResponse` returns a commit when the votes are a quorum of the cluster-manager's current last committed
configuration and of its last published configuration (`isPublishQuorum`, CS:156-158). In a stable publication the last
published configuration stays `s.lastAcceptedConfiguration`, but the last committed configuration can take four values
(`pub_c`): the initial last committed or last accepted configuration of `c`, or `s`'s last committed or last accepted
configuration. Applying the commit of its accepted state, which Java's `handleCommit` allows while a publication is in
flight (D1, finding 1 of the safety mission), copies `c`'s last accepted configuration into its last committed one;
accepting its own publication installs `s`'s configurations, which can move the last committed configuration back
(finding 2 of the safety mission).

Example. Let `s` have last committed configuration {1,2,3} and last accepted configuration {1,2,4} (a reconfiguration
in flight, so its accepted configuration is that of `c`'s accepted state), and let the cluster-manager 1 have applied
the commit of its accepted state before the period, so that its configurations are {1,2,4} and {1,2,4}. `Q` = {2,4} is a
quorum of {1,2,4}, not of {1,2,3}. In the stable period node 1 accepts `s` (its last committed configuration is {1,2,3}
again), nodes 2 and 4 accept `s` and acknowledge it, and node 1 counts both acknowledgements: the votes {2,4} are not a
quorum of {1,2,3}, and no commit is sent. All of `Q` is counted and the publication is not committed, so the hypothesis
on `s.lastCommittedConfiguration` cannot be dropped. Had node 1 counted the acknowledgements before accepting `s`, the
commit would have been sent (the order of finding 1).

Right after `handleClientValue` the four configurations reduce to the cluster-manager's own two and the new accepted
configuration (the asserted precondition `clientValueContract` copies the committed configuration into `s`), and
`publishVotes` is empty, as `publication_committed` requires.

## Proof structure

All in `Sol_OpenSearchProgress_all.lean`, private unless stated.

- Infrastructure: `set_node_self`, `set_node_ne`, `send_node`; stable steps are steps (`estep_step`, `pstep_step`,
  `step_sent`, `eexec_reach`, `pexec_reach`, `pexec_sent`); quorum facts (`filter_length_mono`, `quorum_mono`,
  `hasQuorum_nil`, `ne_nil_of_hasQuorum`, `hasQuorum_of_isEmpty`, `addVote_mem`); the handlers' effects as record
  equations (`spec_setInitialState`, `spec_startJoin`, `spec_join`, `spec_clientValue`, `spec_publish`,
  `spec_respond`, `spec_commit`, `markCommitted_spec`, `markCommitted_mv`, `vomv_pos`, `markCommitted_vomv`); the
  handlers succeed when their checks pass (`startJoin_ok`, `join_ok`, `publish_ok`, `respond_ok`, `respond_quorum`);
  `localNode_id`.
- A reachable fact: `reach_responded`, by induction over `Reachable`: an eligible node whose accepted state has term at
  least 1 has sent a publish response for its accepted (term, version). Only `handlePublishRequest` installs such a
  state, and it sends the response; commits and restarts keep term and version.
- Elections: `elect_c` (the candidate's accepted term, version, metadata version and last accepted configuration are
  constant, its last committed configuration is the initial one or the initial last accepted one, and it has started a
  join once past its initial term), `elect_q` (voters' states and their joins for `t` to the candidate stay no fresher
  than the candidate's initial state), `vote_core` (= `election_vote_accepted`), `won_core` (= `election_won`, from the
  invariant's `not_won_no_quorum`), `elect_sj_phase` and `elect_join_phase` (inductions over the voters), and
  `possible_core` (= `election_possible`).
- Publications: `pub_init` (at the start, `c`'s last published configuration is `s`'s accepted one, and every other
  publication of term `t` is at most `c`'s accepted key, from `leader_settled`, `leader_inflight`, `leader_pubs`,
  `pub_unique`, `inv_descends_parent`, `inv_descends_key`), `pub_c` (`c` stays elected in term `t` with the same last
  published version and configuration, a join at `c` keeping its votes an election quorum by `won_quorum`,
  `quorum_mono` and the default strategy, so that in the model Java's assertion that a join never ends a won election,
  CS:323, holds for `c`; its configurations stay among the four; it can accept no publication of term `t` but `s`),
  `pub_q_ready` (a node of `Q` in term `t` that rejects `s` has already acknowledged it to `c`, from
  `reach_responded`, `response_published`, `won_unique`, `leader_pubs`), `pub_quorum`, `commit_track` (committed, or
  some member of `Q` not yet counted; gives `publication_committed`), `pub_accept_phase`, `pub_count_phase` and
  `pub_possible_core` (= `publication_possible`; the final step re-delivers one acknowledgement).

## How the missions connect

**Pre-vote, then a stable election.** `OpenSearchPreVote.preVote_then_election` predicts the success of the election a
pre-voting round starts, provided nothing changes. The progress theorems keep its core, a quorum of voters no fresher
than the candidate, and let the rest of the cluster run. A round of `c` that has started an election yields the
hypotheses of the election theorems when its senders have not changed since answering: take `Q` the ids of the round's
votes (its eligible recorded senders) at the step that called `startElection`, and
`t = startElectionTerm currentTerm maxTermSeen`. Then `Q` is an election quorum of both configurations of the round's
accepted state, `c`'s (`round_start_quorum`, default strategy); every recorded response is `NoFresher` than
that state (`round_entries`), which is the comparison of `hfresh`, since a response carries the sender's
version-or-metadata-version; and `t` exceeds `c`'s current term and every recorded response's current term, because
`maxTermSeen` is at least each of them (`updateMaxTermSeen`). This is an informal composition: no theorem combines the
two missions, and "unchanged since answering" is itself a stability assumption.

**A stable election, then a stable publication.** The winner's join votes are a quorum of its two configurations (the
invariant's `won_quorum`), `handleClientValue` requires them to be a quorum of the new accepted configuration and the
contract copies the committed one, so right after its first publication the join votes can serve as `Q` in
`publication_committed` and `publication_possible`. The voters handled the start-join for `t`, so they are in term `t`
unless a request of a higher term has reached them since (`publication_possible` assumes terms at most `t` at the
start). Again informal: no theorem chains the two periods, and the winner must first publish (`handleClientValue`
succeeds only under its own guards).

**Timers, uncontested rounds, stable elections.** `OpenSearchElectionTimer` bounds the probability that no candidate's
timer fires at least `δ` before every other. If one fires `δ` ahead and its pre-voting round and election complete
within `δ`, no competing start-join request is issued meanwhile (a candidate sends start-join requests only after its
own pre-voting round succeeds), which is the main exclusion of a stable election; afterwards, once a quorum of a later
candidate's configurations follows the new cluster-manager, that candidate's pre-voting rounds start no election
(`OpenSearchPreVote.no_disruption`). The step "uncontested round with margin `δ` implies a stable election period" is
informal: the model has no time, and message delays are not bounded anywhere.

## Observations

- **Competing candidates for `t`.** The election period excludes other candidates' start-join requests for `t` but not
  the joins those requests produced: a node that handled a competitor's request before the period may have its join
  delivered to the competitor during it. Whatever such joins do, at any cluster of the period where `election_won`
  concludes, `c` has won `t`, and the safety invariant's `won_unique` (which holds there by `reachable_inv`) says that
  no other node has won `t` there or ever sent a publication of term `t`. This is a consequence of the theorems, not a
  separate statement.
- **The candidate votes for itself.** `Q` may contain `c`; the witness of `election_possible` starts with `c`'s own
  start-join, whose join is addressed to `c`. Likewise `c` may belong to the acknowledging `Q` of a publication.
- **`publication_possible` needs no empty votes.** Its witness counts every acknowledgement and then handles one of them
  once more, which finds the votes complete whatever had been counted before.

## Checks

- `lake env lean` on a copy of `Sol_OpenSearchProgress_all.lean` with `#print axioms` for the six theorems: no errors;
  each depends on `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`, the `sorryAx` coming from the four imported
  safety stubs.
- End to end without stubs: scratch modules chaining copies of `Sol_OpenSearchSafety_static_all.lean`,
  `Sol_OpenSearchSafety_steps_all.lean`, `Sol_OpenSearchSafety_all.lean` and `Sol_OpenSearchProgress_all.lean`, each
  stub import replaced by the preceding module: the six theorems depend only on `propext`, `Classical.choice` and
  `Quot.sound`. The four files contain no `sorry`, `native_decide`, `bv_decide` or custom syntax.
- The six split files compile without errors; their only `sorry`s are the imported `Theorems/` stubs. Their
  `import Theorems.Thm_OpenSearchProgress_...` lines fix `ORDER` in the items file: `election_possible` imports
  `election_vote_accepted` and `election_won`, and `publication_possible` imports `publication_committed`, because the
  split tool detects dependencies by name and the docstrings of the two witness theorems name them; the proofs
  themselves use private lemmas only.

## What is not proved

- **That a real cluster reaches a stable period.** Nothing says that the network eventually becomes partially
  synchronous, how long a period lasts, or how long its steps take; the model has no time and no fairness, and the
  theorems are about finite executions.
- **The links to pre-voting and to the timers**, above: "a successful pre-voting round with unchanged senders gives the
  election hypotheses", "the winner's first publication gives the publication hypotheses" and "an uncontested round
  with margin `δ` gives a stable election period" are informal arguments, not composed theorems.
- **Failure detection.** The `LeaderChecker` and `FollowersChecker` (`cluster.fault_detection.*`), by which nodes notice
  a failed cluster-manager or follower and become candidates, the `LagDetector`, and the publication timeouts
  (`cluster.publish.timeout`) are not modelled; neither is the decision to become a candidate.
- **The `Coordinator`.** As in the safety mission, its calls are argued to be steps; which nodes it sends start-joins,
  publications and commits to, join validation and the mode changes are not transcribed. The witness executions are
  sequences of steps the model allows, not runs of the `Coordinator`.
- **Other progress.** Reconfiguration (the `Reconfigurator`, voting-configuration exclusions), the application of
  committed states at the nodes, the remote cluster-state store, plugin election strategies.
- **Failed remote commit writes.** With a remote cluster-state store configured, `handlePublishResponse`, once the
  counted votes form a publish quorum, marks the published state as committed in the store before returning the commit
  (`handlePreCommit`, CS:503-510, 593-599; `RemotePersistedState.markLastAcceptedStateAsCommitted`,
  GatewayMetaState.java:830-864, remote write at 848-853); if that write fails, the method throws after counting the
  vote (GatewayMetaState.java:861-862, 875-877) and no commit is sent, where the transcription returns the commit. For
  safety this is message loss (`NOTES_OpenSearchCoordination.md`, item 7); for progress it is not: in OpenSearch the
  acknowledgement that completes a quorum can be counted without a commit being sent. Read for OpenSearch, the
  publication theorems therefore presuppose that this write succeeds or that no remote cluster-state store is
  configured. The remote update in `handlePublishRequest` (CS:454-456, 617-632), which item 7 also lists, cannot fail
  after the local acceptance (CS:453): it is made only at a node that is not the cluster-manager of the incoming state,
  where `RemotePersistedState.setLastAcceptedState` only records the state in memory (GatewayMetaState.java:748-753).
