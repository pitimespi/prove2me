# Read-back: `OpenSearchCoordination.addVote_eligible`

## Notions used

**Nodes.** A node $n$ (`DiscoveryNode`) has an id $n.\mathrm{id} \in \mathbb{N}$ and a Boolean flag $n.\mathrm{isClusterManagerNode}$, read as "eligible to vote".

**Vote collections.** A vote collection $v$ is a list $v.\mathrm{nodes}$ of natural numbers. $\mathrm{addVote}(v, n)$ returns a pair:

- if $n.\mathrm{isClusterManagerNode} = \mathrm{true}$ and $n.\mathrm{id} \notin v.\mathrm{nodes}$, it returns $(\langle n.\mathrm{id} :: v.\mathrm{nodes}\rangle,\ \mathrm{true})$;
- otherwise it returns $(v,\ \mathrm{false})$.

The first component is the new collection. The second says whether the vote was added.

## 1. Declaration

**Binders.**
- $v$: a vote collection;
- $n$: a node;
- $x$: a natural number (`NodeId`).

**Hypotheses.** None.

**Conclusion.**
$$x \in \mathrm{addVote}(v, n).1.\mathrm{nodes} \iff x \in v.\mathrm{nodes} \;\vee\; \big(x = n.\mathrm{id} \wedge n.\mathrm{isClusterManagerNode} = \mathrm{true}\big).$$
After adding $n$'s vote, the ids in the collection are exactly the previous ids, plus $n.\mathrm{id}$ when $n$ is eligible.

## 2. What is not constrained

- The statement is about **membership only**.
  - It says nothing about the second component (the "added" Boolean).
  - It says nothing about order or multiplicity in the new list. For example, it does not state that a vote from an already-present id leaves the list unchanged, although by definition it does.
- $v$ is arbitrary. It may already contain duplicates, or ids of ineligible nodes; the statement still holds.
- There are no hypotheses, so nothing can make the statement vacuous.

## 3. Plain-language summary

Adding a vote from node $n$ adds $n$'s id to the set of voters if and only if $n$ is cluster-manager-eligible. Votes from ineligible nodes are ignored, and no existing voter is removed.
