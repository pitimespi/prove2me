# Read-back: `OpenSearchCoordination.no_votes_no_quorum`

## Notions used

**Voting configurations.** A voting configuration $c$ is a strictly increasing list $c.\mathrm{nodeIds}$ of natural numbers.

**Quorum test.** For a list $L$ of naturals:
$$\mathrm{hasQuorum}(c, L) = \mathrm{true} \iff 2\cdot\big|[\,x \in c.\mathrm{nodeIds} \mid x \in L\,]\big| > |c.\mathrm{nodeIds}|.$$

**Vote collections.** A vote collection $v$ is a list $v.\mathrm{nodes}$ of natural numbers. $\mathrm{VoteCollection.empty}$ is the collection with the empty list. $\mathrm{isQuorum}(v, c) := \mathrm{hasQuorum}(c, v.\mathrm{nodes})$.

## 1. Declaration

**Binders.** $c$: a voting configuration.

**Hypotheses.** None.

**Conclusion.** $\mathrm{isQuorum}(\mathrm{VoteCollection.empty}, c) = \mathrm{false}$, that is, $\mathrm{hasQuorum}(c, [\,]) = \mathrm{false}$.

Unfolded, no entry of $c.\mathrm{nodeIds}$ occurs in $[\,]$, so the filtered length is $0$, and $2 \cdot 0 > |c.\mathrm{nodeIds}|$ is false.

## 2. What is not constrained

- $c$ is arbitrary, including the empty configuration (where $0 > 0$ is false).
- There are no hypotheses. The content is a direct computation from the definition.

## 3. Plain-language summary

An empty vote collection is not a quorum of any voting configuration.
