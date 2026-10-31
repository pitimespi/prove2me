# Read-back: `OpenSearchPreVote.votes_mem`

## Notions used

**Discovery nodes.** A discovery node $n$ is a pair: a node id $n.\mathrm{id} \in \mathbb{N}$ and a Boolean $n.\mathrm{cm}$ ("cluster-manager-eligible").

**Pre-voting rounds.** A round $r$ has five fields:
- a cluster state;
- a local node;
- a list $r.\mathrm{preVotesReceived}$ of pairs $(\mathit{sender}, \mathit{response})$;
- two Booleans, $\mathrm{electionStarted}$ and $\mathrm{isClosed}$.

**Vote collections and $\mathrm{votes}(r)$.** A vote collection is a list of node ids. $\mathrm{addVote}(v, n)$ prepends $n.\mathrm{id}$ to $v$ when $n.\mathrm{cm}$ is true and $n.\mathrm{id}$ is not already in $v$; otherwise it leaves $v$ unchanged. $\mathrm{votes}(r)$ is computed as follows:
- start from the empty collection;
- fold $\mathrm{addVote}$ over the senders of $r.\mathrm{preVotesReceived}$, from the last entry to the first (`foldr`);
- the responses play no part.

## 1. Declaration

**Binders.** There are no hypotheses.
- $V$: an implicit type;
- $r$: a pre-voting round over $V$, completely arbitrary (not assumed reachable);
- $x$: a node id.

**Conclusion.**
$$x \in \mathrm{votes}(r).\mathrm{nodes} \iff \exists\, p \in r.\mathrm{preVotesReceived},\ p.1.\mathrm{id} = x \wedge p.1.\mathrm{cm} = \mathrm{true}.$$

The vote collection of the round contains the id $x$ exactly when some received entry has a sender with id $x$ that is cluster-manager-eligible.

## 2. What is not constrained

- **The round.** $r$ is arbitrary. The list may contain repeated senders, or two senders with the same id and different flags (for example $\langle 5,\mathrm{false}\rangle$ and $\langle 5,\mathrm{true}\rangle$, which give the vote $5$ through the second). The round may be closed or started.
- **Order and multiplicity.** The statement is about membership only. It says nothing about the order or multiplicity of $\mathrm{votes}(r).\mathrm{nodes}$. By construction the list has no duplicates, but the theorem does not state it.
- **The responses.** The responses $p.2$ do not occur. Their terms and versions do not affect which ids count.
- **Vacuity.** There are no hypotheses, so nothing can be vacuous.

## 3. Plain-language summary

The ids counted as votes by a pre-voting round are exactly the ids of the cluster-manager-eligible senders that appear in its list of received pre-votes. Ineligible senders and the contents of the responses contribute nothing.
