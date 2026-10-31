# Read-back: `OpenSearchCoordination.handleCommit_spec`

## Notions used

**Coordination states and cluster states.** A coordination state $cs$ has nine fields: localNode, currentTerm $\in\mathbb{N}$, lastAcceptedState, joinVotes, startedJoinSinceLastReboot, electionWon, lastPublishedVersion $\in\mathbb{Z}$, lastPublishedConfiguration and publishVotes.

A cluster state $S$ has nine independent fields:

- $S.\mathrm{term} \in \mathbb{N}$;
- $S.\mathrm{version} \in \mathbb{Z}$ and $S.\mathrm{metadataVersion} \in \mathbb{Z}$;
- two voting configurations, $S.\mathrm{lastCommittedConfiguration}$ and $S.\mathrm{lastAcceptedConfiguration}$;
- $S.\mathrm{clusterManagerNode}$, an optional natural;
- two Booleans, $S.\mathrm{clusterUUIDKnown}$ and $S.\mathrm{clusterUUIDCommitted}$;
- a payload $S.\mathrm{value}$.

Abbreviations, read from $cs.\mathrm{lastAcceptedState}$:

- $\mathrm{lat}(cs)$ = its term;
- $\mathrm{lav}(cs)$ = its version;
- $\mathrm{C}(cs)$ = its last committed configuration;
- $\mathrm{A}(cs)$ = its last accepted configuration.

**Marking committed.** $\mathrm{markCommitted}(S)$ works in two steps:

1. If the two configurations differ, set the committed configuration to the accepted one.
2. If $\mathrm{clusterUUIDKnown} = \mathrm{true}$ and $\mathrm{clusterUUIDCommitted} = \mathrm{false}$, set $\mathrm{clusterUUIDCommitted} := \mathrm{true}$.

The net effect: the committed configuration becomes the accepted configuration, and $\mathrm{clusterUUIDCommitted}$ becomes $\mathrm{clusterUUIDCommitted} \vee \mathrm{clusterUUIDKnown}$. The other seven fields are unchanged.

**Messages.** A commit request $c$ has a node $c.\mathrm{sourceNode}$, a term $c.\mathrm{term} \in \mathbb{N}$ and a version $c.\mathrm{version} \in \mathbb{Z}$.

**The handler** $\mathrm{handleCommit}(cs, c)$ checks three guards in order:

1. If $c.\mathrm{term} \ne cs.\mathrm{currentTerm}$, it returns $\mathrm{error}$.
2. If $c.\mathrm{term} \ne \mathrm{lat}(cs)$, it returns $\mathrm{error}$.
3. If $c.\mathrm{version} \ne \mathrm{lav}(cs)$, it returns $\mathrm{error}$.

Otherwise it returns $\mathrm{ok}(cs \text{ with } \mathrm{lastAcceptedState} := \mathrm{markCommitted}(cs.\mathrm{lastAcceptedState}))$.

## 1. Declaration

**Binders.** $V$ (implicit), $cs$, $c$ (a commit request), $cs'$.

**Hypothesis.** $h$: $\mathrm{handleCommit}(cs, c) = \mathrm{ok}(cs')$.

**Conclusion.** The conjunction of:

1. $c.\mathrm{term} = cs.\mathrm{currentTerm}$;
2. $c.\mathrm{term} = \mathrm{lat}(cs)$;
3. $c.\mathrm{version} = \mathrm{lav}(cs)$;
4. $cs' = cs \text{ with } \mathrm{lastAcceptedState} := \mathrm{markCommitted}(cs.\mathrm{lastAcceptedState})$;
5. $\mathrm{C}(cs') = \mathrm{A}(cs')$;
6. $\mathrm{A}(cs') = \mathrm{A}(cs)$;
7. $\mathrm{lat}(cs') = \mathrm{lat}(cs)$;
8. $\mathrm{lav}(cs') = \mathrm{lav}(cs)$;
9. $cs'.\mathrm{lastAcceptedState}.\mathrm{value} = cs.\mathrm{lastAcceptedState}.\mathrm{value}$.

Conjunct 4 determines $cs'$ completely. Conjuncts 5–9 spell out consequences of it. Conjuncts 1 and 2 together give $cs.\mathrm{currentTerm} = \mathrm{lat}(cs)$: a commit is applied only when the node's last-accepted term equals its current term.

## 2. What is not constrained

- $c.\mathrm{sourceNode}$ is never mentioned. The handler does not read it.
- Some effects of $\mathrm{markCommitted}$ are implied only through conjunct 4 and are not stated separately:
  - the update of $\mathrm{clusterUUIDCommitted}$;
  - the preservation of $\mathrm{metadataVersion}$, $\mathrm{clusterManagerNode}$ and $\mathrm{clusterUUIDKnown}$.
- The statement goes in one direction only: from success to the listed facts.
- No hypothesis beyond success is assumed. No invariant on $cs$ is needed or used.
- The statement is not vacuous: any $cs$ with $cs.\mathrm{currentTerm} = \mathrm{lat}(cs)$ and $c = \langle \_, \mathrm{lat}(cs), \mathrm{lav}(cs)\rangle$ succeeds.

## 3. Plain-language summary

A commit is applied only when its term equals both the node's current term and its last-accepted term, and its version equals the last-accepted version. Applying it only marks the last-accepted state as committed:

- the committed configuration becomes the accepted configuration;
- a known cluster UUID is flagged committed;
- the term, version, accepted configuration and payload are unchanged.
