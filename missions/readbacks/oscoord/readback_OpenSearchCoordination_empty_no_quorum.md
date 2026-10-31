# Read-back: `OpenSearchCoordination.empty_no_quorum`

## Notions used

**Voting configurations.** A voting configuration $c$ is a strictly increasing list $c.\mathrm{nodeIds}$ of natural numbers. $\mathrm{EMPTY\_CONFIG}$ is the configuration whose list is $[\,]$. Configurations are equal iff their lists are equal, so every configuration with an empty list *is* $\mathrm{EMPTY\_CONFIG}$.

**Quorum test.** For a list $L$ of naturals:
$$\mathrm{hasQuorum}(c, L) = \mathrm{true} \iff 2\cdot\big|[\,x \in c.\mathrm{nodeIds} \mid x \in L\,]\big| > |c.\mathrm{nodeIds}|.$$

## 1. Declaration

**Binders.** $a$: a list of natural numbers.

**Hypotheses.** None.

**Conclusion.** $\mathrm{hasQuorum}(\mathrm{EMPTY\_CONFIG}, a) = \mathrm{false}$.

Unfolded, the sublist of $[\,]$ has length $0$, and the test $2 \cdot 0 > 0$ is false.

## 2. What is not constrained

- $a$ is arbitrary, and the conclusion holds for every list, including very long ones.
- There are no hypotheses, so nothing can make the statement vacuous.
- The content is a direct computation from the definition.
- The theorem itself states only the fact about $\mathrm{hasQuorum}$. Elsewhere in the definitions, election and publish quorums require a quorum of several configurations at once. So, by the definitions rather than by this statement, a state whose committed, accepted or published configuration is empty can never reach the corresponding quorum.

## 3. Plain-language summary

The empty voting configuration has no quorum: no list of votes, however large, counts as more than half of zero voters.
